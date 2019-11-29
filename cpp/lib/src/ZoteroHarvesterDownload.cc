/** \brief Classes related to the Zotero Harvester's download API
 *  \author Madeeswaran Kannan
 *
 *  \copyright 2019 Universitätsbibliothek Tübingen.  All rights reserved.
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as
 *  published by the Free Software Foundation, either version 3 of the
 *  License, or (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include "StringUtil.h"
#include "ZoteroHarvesterDownload.h"
#include "util.h"


namespace ZoteroHarvester {


namespace Download {


namespace DirectDownload {


static void PostToTranslationServer(const Url &translation_server_url, const unsigned time_limit, const std::string &user_agent,
                                    const std::string &request_body, const bool request_is_json, std::string * const response_body, unsigned * response_code,
                                    std::string * const error_message)
{
    Downloader::Params downloader_params;
    downloader_params.user_agent_ = user_agent;
    downloader_params.additional_headers_ = { "Accept: application/json",
                                              std::string("Content-Type: ") + (request_is_json ? "application/json" : "text/plain") };
    downloader_params.post_data_ = request_body;

    const Url endpoint_url(translation_server_url.toString() + "/web");
    Downloader downloader(endpoint_url, downloader_params, time_limit);
    if (downloader.anErrorOccurred()) {
        *response_code = 0;
        *error_message = downloader.getLastErrorMessage();

        LOG_DEBUG("failed to fetch response from the translation server! error: " + *error_message);
        return;
    }

    *response_body = downloader.getMessageBody();
    *response_code = downloader.getResponseCode();
}


static void QueryRemoteUrl(const std::string &url, const unsigned time_limit, const bool ignore_robots_dot_txt,
                           const std::string &user_agent, std::string * const response_header, std::string * const response_body,
                           unsigned * response_code, std::string * const error_message)
{
    Downloader::Params downloader_params;
    downloader_params.user_agent_ = user_agent;
    downloader_params.honour_robots_dot_txt_ = not ignore_robots_dot_txt;

    Downloader downloader(url, downloader_params, time_limit);
    if (downloader.anErrorOccurred()) {
        *response_code = 0;
        *error_message = downloader.getLastErrorMessage();

        LOG_DEBUG("failed to fetch response from remote url '" + url + "'! error: " + *error_message);
        return;
    }

    *response_body = downloader.getMessageBody();
    *response_header = downloader.getMessageHeader();
    *response_code = downloader.getResponseCode();
}


void Tasklet::run(const Params &parameters, Result * const result) {
    LOG_INFO("Harvesting URL " + parameters.download_item_.toString());

    if (parameters.operation_ == Operation::USE_TRANSLATION_SERVER) {
        PostToTranslationServer(parameters.translation_server_url_, parameters.time_limit_, parameters.user_agent_,
                                parameters.download_item_.url_, /* request_is_json = */ false, &result->response_body_,
                                &result->response_code_, &result->error_message_);

        // 300 => multiple matches found, try to harvest children (send the response_body right back to the server, to get all of them)
        if (result->response_code_ == 300) {
            LOG_DEBUG("multiple articles found => trying to harvest children");
            PostToTranslationServer(parameters.translation_server_url_, parameters.time_limit_, parameters.user_agent_,
                                    result->response_body_, /* request_is_json = */ true, &result->response_body_,
                                    &result->response_code_, &result->error_message_);
        }
    } else {
        QueryRemoteUrl(parameters.download_item_.url_, parameters.time_limit_, parameters.ignore_robots_dot_txt_,
                       parameters.user_agent_, &result->response_header_, &result->response_body_, &result->response_code_,
                       &result->error_message_);
    }

    if (result->downloadSuccessful()) {
        download_manager_->addToDownloadCache(parameters.download_item_.url_.toString(), result->response_body_,
                                            result->response_header_, result->response_code_, result->error_message_,
                                            parameters.operation_);
    }
}


Tasklet::Tasklet(ThreadUtil::ThreadSafeCounter<unsigned> * const instance_counter, DownloadManager * const download_manager,
                 std::unique_ptr<Params> parameters)
 : Util::Tasklet<Params, Result>(instance_counter, parameters->download_item_,
                                 "DirectDownload: " + parameters->download_item_.url_.toString(),
                                 std::bind(&Tasklet::run, this, std::placeholders::_1, std::placeholders::_2),
                                 std::unique_ptr<Result>(new Result(parameters->download_item_, parameters->operation_)),
                                 std::move(parameters)),
   download_manager_(download_manager) {}


} // end namespace DirectDownload


namespace Crawling {


bool Tasklet::downloadIntermediateUrl(const std::string &url, const SimpleCrawler::Params &/* unused */,
                                      SimpleCrawler::PageDetails * const page_details, const Params &parameters) const
{
    const auto new_download_item(parameters.harvestable_manager_->newHarvestableItem(url, parameters.download_item_.journal_));
    auto future(download_manager_->directDownload(new_download_item, parameters.user_agent_, DirectDownload::Operation::DIRECT_QUERY,
                                                  parameters.per_crawl_url_time_limit_));

    const auto &download_result(future->getResult());
    if (not download_result.downloadSuccessful()) {
        page_details->error_message_ = download_result.error_message_;
        return false;
    }

    page_details->body_ = download_result.response_body_;
    page_details->header_= download_result.response_header_;
    page_details->url_ = url;
    return true;
}


void Tasklet::run(const Params &parameters, Result * const result) {
    LOG_INFO("Crawling URL " + parameters.download_item_.toString());

    SimpleCrawler::Params crawler_params;
    crawler_params.ignore_robots_dot_txt_ = parameters.ignore_robots_dot_txt_;
    crawler_params.timeout_ = parameters.per_crawl_url_time_limit_;
    crawler_params.user_agent_ = parameters.user_agent_;
    crawler_params.print_queued_urls_ = true;
    crawler_params.print_skipped_urls_ = true;

    SimpleCrawler::SiteDesc site_desc;
    site_desc.start_url_ = parameters.download_item_.url_;
    site_desc.max_crawl_depth_ = parameters.download_item_.journal_.crawl_params_.max_crawl_depth_;

    std::string crawl_url_regex_str;
    if (parameters.download_item_.journal_.crawl_params_.crawl_url_regex_ != nullptr)
        crawl_url_regex_str = parameters.download_item_.journal_.crawl_params_.crawl_url_regex_->getPattern();

    if (not crawl_url_regex_str.empty()) {
        // the crawl URL regex needs to be combined with the extraction URL regex if they aren't the same
        // we combine the two here to prevent unnecessary duplication in the config file
        const auto extraction_url_regex_pattern(parameters.download_item_.journal_.crawl_params_.extraction_regex_ != nullptr ?
                                                parameters.download_item_.journal_.crawl_params_.extraction_regex_->getPattern() : "");

        if (not extraction_url_regex_pattern.empty() and extraction_url_regex_pattern != crawl_url_regex_str)
            crawl_url_regex_str = "((" + crawl_url_regex_str + ")|(" + extraction_url_regex_pattern + "))";

        site_desc.url_regex_matcher_.reset(RegexMatcher::RegexMatcherFactoryOrDie(crawl_url_regex_str));
    }

    TimeLimit crawl_process_time_limit(parameters.total_crawl_time_limit_);

    // the crawler plugs into the download manager's queuing and download-delay infrastructure
    SimpleCrawler crawler(site_desc, crawler_params,
                          std::bind(&Tasklet::downloadIntermediateUrl, this, std::placeholders::_1, std::placeholders::_2,
                                    std::placeholders::_3, std::cref(parameters)));

    SimpleCrawler::PageDetails page_details;
    unsigned num_crawled_urls(0), num_queued_urls(0);

    while (not crawl_process_time_limit.limitExceeded() and crawler.getNextPage(&page_details)) {
        ++num_crawled_urls;
        if (page_details.error_message_.empty()) {
            const auto url(page_details.url_);
            if (parameters.download_item_.journal_.crawl_params_.extraction_regex_ == nullptr
                or parameters.download_item_.journal_.crawl_params_.extraction_regex_->match(url))
            {
                const auto new_download_item(parameters.harvestable_manager_->newHarvestableItem(page_details.url_,
                                                                                                 parameters.download_item_.journal_));
                result->downloaded_items_.emplace_back(download_manager_->directDownload(new_download_item, parameters.user_agent_,
                                                                                         DirectDownload::Operation::USE_TRANSLATION_SERVER));
                ++num_queued_urls;
            }
        }
    }

    if (crawl_process_time_limit.limitExceeded())
        LOG_WARNING("process timed-out - not all URLs were crawled");

    LOG_INFO("crawled " + std::to_string(num_crawled_urls) + " URLs, queued "
             + std::to_string(num_queued_urls) + " URLs for extraction");
}


Tasklet::Tasklet(ThreadUtil::ThreadSafeCounter<unsigned> * const instance_counter, DownloadManager * const download_manager,
                 std::unique_ptr<Params> parameters)
 : Util::Tasklet<Params, Result>(instance_counter, parameters->download_item_,
                                 "Crawling: " + parameters->download_item_.url_.toString(),
                                 std::bind(&Tasklet::run, this, std::placeholders::_1, std::placeholders::_2),
                                 std::unique_ptr<Result>(new Result()), std::move(parameters)),
   download_manager_(download_manager) {}


} // end namespace Crawling


namespace RSS {


bool Tasklet::feedNeedsToBeHarvested(const std::string &feed_contents, const Config::JournalParams &journal_params,
                                     const SyndicationFormat::AugmentParams &syndication_format_site_params) const
{
    if (force_downloads_)
        return true;

    const auto last_harvest_timestamp(upload_tracker_.getLastUploadTime(journal_params.name_));
    if (last_harvest_timestamp == TimeUtil::BAD_TIME_T) {
        LOG_DEBUG("feed will be harvested for the first time");
        return true;
    } else {
        const auto diff((time(nullptr) - last_harvest_timestamp) / 86400);
        if (unlikely(diff < 0))
            LOG_ERROR("unexpected negative time difference '" + std::to_string(diff) + "'");

        const auto harvest_threshold(journal_params.update_window_ > 0 ? journal_params.update_window_ : feed_harvest_interval_);
        LOG_DEBUG("feed last harvest timestamp: " + TimeUtil::TimeTToString(last_harvest_timestamp));
        LOG_DEBUG("feed harvest threshold: " + std::to_string(harvest_threshold) + " days | diff: " + std::to_string(diff) + " days");

        if (diff >= harvest_threshold) {
            LOG_DEBUG("feed older than " + std::to_string(harvest_threshold) +
                      " days. flagging for mandatory harvesting");
            return true;
        }
    }

    // needs to be parsed again as iterating over a SyndicationFormat instance will consume its items
    std::string err_msg;
    const auto syndication_format(SyndicationFormat::Factory(feed_contents, syndication_format_site_params, &err_msg));
    if (syndication_format == nullptr) {
        LOG_WARNING("problem parsing XML document for RSS feed '" + getParameter().download_item_.url_.toString() + "': "
                    + err_msg);
        return false;
    }

    for (const auto &item : *syndication_format) {
        const auto pub_date(item.getPubDate());
        if (force_process_feeds_with_no_pub_dates_ and pub_date == TimeUtil::BAD_TIME_T) {
            LOG_DEBUG("URL '" + item.getLink() + "' has no publication timestamp. flagging for harvesting");
            return true;
        } else if (pub_date != TimeUtil::BAD_TIME_T and std::difftime(item.getPubDate(), last_harvest_timestamp) > 0) {
            LOG_DEBUG("URL '" + item.getLink() + "' was added/updated since the last harvest of this RSS feed. flagging for harvesting");
            return true;
        }
    }

    LOG_INFO("no new, harvestable entries in feed. skipping...");
    return false;
}


void Tasklet::run(const Params &parameters, Result * const result) {
    LOG_INFO("Harvesting feed " + parameters.download_item_.toString());

    std::unique_ptr<SyndicationFormat> syndication_format;
    std::string feed_contents, syndication_format_parse_err_msg;
    SyndicationFormat::AugmentParams syndication_format_augment_parameters;
    syndication_format_augment_parameters.strptime_format_ = parameters.download_item_.journal_.strptime_format_string_;

    if (not parameters.feed_contents_.empty())
        feed_contents = parameters.feed_contents_;
    else {
        Downloader::Params downloader_params;
        downloader_params.user_agent_ = parameters.user_agent_;

        Downloader downloader(parameters.download_item_.url_.toString(), downloader_params);
        if (downloader.anErrorOccurred()) {
            LOG_WARNING("could not download RSS feed '" + parameters.download_item_.url_.toString() + "'!");
            return;
        }

        feed_contents = downloader.getMessageBody();
    }

    if (not feedNeedsToBeHarvested(feed_contents, parameters.download_item_.journal_, syndication_format_augment_parameters))
        return;

    syndication_format.reset(SyndicationFormat::Factory(feed_contents, syndication_format_augment_parameters,
                             &syndication_format_parse_err_msg).release());

    if (syndication_format == nullptr) {
        LOG_WARNING("problem parsing XML document for RSS feed '" + parameters.download_item_.url_.toString() + "': "
                    + syndication_format_parse_err_msg);
        return;
    }

    LOG_DEBUG("Title: " + syndication_format->getTitle());

    for (const auto &item : *syndication_format) {
        const auto new_download_item(parameters.harvestable_manager_->newHarvestableItem(item.getLink(), parameters.download_item_.journal_));
        result->downloaded_items_.emplace_back(download_manager_->directDownload(new_download_item, parameters.user_agent_,
                                                                                 DirectDownload::Operation::USE_TRANSLATION_SERVER));
    }
}


Tasklet::Tasklet(ThreadUtil::ThreadSafeCounter<unsigned> * const instance_counter, DownloadManager * const download_manager,
                 std::unique_ptr<Params> parameters, const Util::UploadTracker &upload_tracker, const bool force_downloads,
                 const unsigned feed_harvest_interval, const bool force_process_feeds_with_no_pub_dates)
 : Util::Tasklet<Params, Result>(instance_counter, parameters->download_item_,
                                 "RSS: " + parameters->download_item_.url_.toString(),
                                 std::bind(&Tasklet::run, this, std::placeholders::_1, std::placeholders::_2),
                                 std::unique_ptr<Result>(new Result()), std::move(parameters)),
   download_manager_(download_manager), upload_tracker_(upload_tracker), force_downloads_(force_downloads),
   feed_harvest_interval_(feed_harvest_interval), force_process_feeds_with_no_pub_dates_(force_process_feeds_with_no_pub_dates) {}


} // end namespace RSS


DownloadManager::GlobalParams::GlobalParams(const Config::GlobalParams &config_global_params,
                                            Util::HarvestableItemManager * const harvestable_manager)
 : translation_server_url_(config_global_params.translation_server_url_),
   default_download_delay_time_(config_global_params.download_delay_params_.default_delay_),
   max_download_delay_time_(config_global_params.download_delay_params_.max_delay_),
   rss_feed_harvest_interval_(config_global_params.rss_harvester_operation_params_.harvest_interval_),
   force_process_rss_feeds_with_no_pub_dates_(config_global_params.rss_harvester_operation_params_.force_process_feeds_with_no_pub_dates_),
   ignore_robots_txt_(false), force_downloads_(false), harvestable_manager_(harvestable_manager) {}


DownloadManager::DelayParams::DelayParams(const std::string &robots_dot_txt, const unsigned default_download_delay_time,
                                          const unsigned max_download_delay_time)
 : robots_dot_txt_(robots_dot_txt), time_limit_(robots_dot_txt_.getCrawlDelay("*") * 1000)
{
    if (time_limit_.getLimit() < default_download_delay_time)
        time_limit_ = default_download_delay_time;
    else if (time_limit_.getLimit() > max_download_delay_time)
        time_limit_ = max_download_delay_time;

    time_limit_.restart();
}


DownloadManager::DelayParams::DelayParams(const TimeLimit &time_limit, const unsigned default_download_delay_time,
                                          const unsigned max_download_delay_time)
 : time_limit_(time_limit)
{
    if (time_limit_.getLimit() < default_download_delay_time)
        time_limit_ = default_download_delay_time;
    else if (time_limit_.getLimit() > max_download_delay_time)
        time_limit_ = max_download_delay_time;

    time_limit_.restart();
}


void *DownloadManager::BackgroundThreadRoutine(void * parameter) {
    static const unsigned BACKGROUND_THREAD_SLEEP_TIME(32 * 1000);   // ms -> us

    DownloadManager * const download_manager(reinterpret_cast<DownloadManager *>(parameter));

    while (not download_manager->stop_background_thread_.load()) {
        download_manager->processQueueBuffers();

        // we don't need to lock access to the domain data store
        // as it's exclusively accessed in this background thread
        for (const auto &domain_entry : download_manager->domain_data_) {
            download_manager->processDomainQueues(domain_entry.second.get());
            download_manager->cleanupCompletedTasklets(domain_entry.second.get());
        }

        ::usleep(BACKGROUND_THREAD_SLEEP_TIME);
    }

    pthread_exit(nullptr);
}


DownloadManager::DelayParams DownloadManager::generateDelayParams(const Url &url) {
    const auto hostname(url.getAuthority());
    Downloader robots_txt_downloader(url.getRobotsDotTxtUrl());
    if (robots_txt_downloader.anErrorOccurred()) {
        LOG_DEBUG("couldn't retrieve robots.txt for domain '" + hostname + "'");
        return DelayParams(static_cast<unsigned>(0), global_params_.default_download_delay_time_,
                           global_params_.max_download_delay_time_);
    }

    DelayParams new_delay_params(robots_txt_downloader.getMessageBody(), global_params_.default_download_delay_time_,
                                 global_params_.max_download_delay_time_);

    LOG_DEBUG("set download-delay for domain '" + hostname + "' to " +
              std::to_string(new_delay_params.time_limit_.getLimit()) + " ms");
    return new_delay_params;
}


DownloadManager::DomainData *DownloadManager::lookupDomainData(const Url &url, bool add_if_absent) {
    const auto hostname(url.getAuthority());
    const auto match(domain_data_.find(hostname));
    if (match != domain_data_.end())
        return match->second.get();
    else if (add_if_absent) {
        DomainData * const new_domain_data(new DomainData(generateDelayParams(url)));
        domain_data_.insert(std::make_pair(hostname, new_domain_data));
        return new_domain_data;
    }

    return nullptr;
}


void DownloadManager::processQueueBuffers() {
    // enqueue the tasks in their domain-specific queues
    {
        std::lock_guard<std::recursive_mutex> direct_download_queue_buffer_lock(direct_download_queue_buffer_mutex_);
        while (not direct_download_queue_buffer_.empty()) {
            std::shared_ptr<DirectDownload::Tasklet> tasklet(direct_download_queue_buffer_.front());
            auto domain_data(lookupDomainData(tasklet->getParameter().download_item_.url_, /* add_if_absent = */ true));
            domain_data->queued_direct_downloads_.emplace_back(tasklet);

            direct_download_queue_buffer_.pop_front();
        }
    }

    {
        std::lock_guard<std::recursive_mutex> crawling_queue_buffer_lock(crawling_queue_buffer_mutex_);
        while (not crawling_queue_buffer_.empty()) {
            std::shared_ptr<Crawling::Tasklet> tasklet(crawling_queue_buffer_.front());
            auto domain_data(lookupDomainData(tasklet->getParameter().download_item_.url_, /* add_if_absent = */ true));
            domain_data->queued_crawls_.emplace_back(tasklet);

            crawling_queue_buffer_.pop_front();
        }
    }

    {
        std::lock_guard<std::recursive_mutex> rss_queue_buffer_lock(rss_queue_buffer_mutex_);
        while (not rss_queue_buffer_.empty()) {
            std::shared_ptr<RSS::Tasklet> tasklet(rss_queue_buffer_.front());
            auto domain_data(lookupDomainData(tasklet->getParameter().download_item_.url_, /* add_if_absent = */ true));
            domain_data->queued_rss_feeds_.emplace_back(tasklet);

            rss_queue_buffer_.pop_front();
        }
    }
}


void DownloadManager::processDomainQueues(DomainData * const domain_data) {
    // apply download delays and create tasklets for downloads/crawls
    const bool adhere_to_download_limit(not global_params_.ignore_robots_txt_);

    if (adhere_to_download_limit and not domain_data->delay_params_.time_limit_.limitExceeded())
        return;

    while (not domain_data->queued_direct_downloads_.empty()
           and direct_download_tasklet_execution_counter_ < MAX_DIRECT_DOWNLOAD_TASKLETS)
    {
        std::shared_ptr<DirectDownload::Tasklet> direct_download_tasklet(domain_data->queued_direct_downloads_.front());
        domain_data->active_direct_downloads_.emplace_back(direct_download_tasklet);
        domain_data->queued_direct_downloads_.pop_front();
        direct_download_tasklet->start();

        if (adhere_to_download_limit) {
            domain_data->delay_params_.time_limit_.restart();
            return;
        }
    }

    while (not domain_data->queued_crawls_.empty()
           and crawling_tasklet_execution_counter_ < MAX_CRAWLING_TASKLETS)
    {
        std::shared_ptr<Crawling::Tasklet> crawling_tasklet(domain_data->queued_crawls_.front());
        domain_data->active_crawls_.emplace_back(crawling_tasklet);
        domain_data->queued_crawls_.pop_front();
        crawling_tasklet->start();

        if (adhere_to_download_limit) {
            domain_data->delay_params_.time_limit_.restart();
            return;
        }
    }

    while(not domain_data->queued_rss_feeds_.empty()
          and rss_tasklet_execution_counter_ < MAX_RSS_TASKLETS)
    {
        std::shared_ptr<RSS::Tasklet> rss_tasklet(domain_data->queued_rss_feeds_.front());
        domain_data->active_rss_feeds_.emplace_back(rss_tasklet);
        domain_data->queued_rss_feeds_.pop_front();
        rss_tasklet->start();

        if (adhere_to_download_limit) {
            domain_data->delay_params_.time_limit_.restart();
            return;
        }
    }
}


void DownloadManager::cleanupCompletedTasklets(DomainData * const domain_data) {
    for (auto iter(domain_data->active_direct_downloads_.begin()); iter != domain_data->active_direct_downloads_.end();) {
        if ((*iter)->isComplete()) {
            iter = domain_data->active_direct_downloads_.erase(iter);
            continue;
        }
        ++iter;
    }

    for (auto iter(domain_data->active_crawls_.begin()); iter != domain_data->active_crawls_.end();) {
        if ((*iter)->isComplete()) {
            iter = domain_data->active_crawls_.erase(iter);
            continue;
        }
        ++iter;
    }

    for (auto iter(domain_data->active_rss_feeds_.begin()); iter != domain_data->active_rss_feeds_.end();) {
        if ((*iter)->isComplete()) {
            iter = domain_data->active_rss_feeds_.erase(iter);
            continue;
        }
        ++iter;
    }
}


std::unique_ptr<DirectDownload::Result> DownloadManager::fetchDownloadDataFromCache(const Util::HarvestableItem &source,
                                                                                    const DirectDownload::Operation operation) const
{
    std::lock_guard<std::recursive_mutex> download_cache_lock(cached_download_data_mutex_);

    const auto cache_hit(cached_download_data_.equal_range(source.url_.toString()));
    for (auto itr(cache_hit.first); itr != cache_hit.second; ++itr) {
        if (itr->second.operation_ == operation) {
            std::unique_ptr<DirectDownload::Result> cached_result(new DirectDownload::Result(source, operation));

            cached_result->response_body_ = itr->second.response_body_;
            cached_result->response_header_ = itr->second.response_header_;
            cached_result->response_code_ = itr->second.response_code_;
            cached_result->error_message_ = itr->second.error_message_;

            return cached_result;
        }
    }

    return nullptr;
}


DownloadManager::DownloadManager(const GlobalParams &global_params)
 : global_params_(global_params), stop_background_thread_(false)
{
    if (::pthread_create(&background_thread_, nullptr, BackgroundThreadRoutine, this) != 0)
        LOG_ERROR("background download manager thread creation failed!");
}


DownloadManager::~DownloadManager() {
    stop_background_thread_.store(true);
    const auto retcode(::pthread_join(background_thread_, nullptr));
    if (retcode != 0)
        LOG_WARNING("couldn't join with the download manager background thread! result = " + std::to_string(retcode));

    domain_data_.clear();
    cached_download_data_.clear();
    direct_download_queue_buffer_.clear();
    rss_queue_buffer_.clear();
    crawling_queue_buffer_.clear();
}


std::unique_ptr<Util::Future<DirectDownload::Params, DirectDownload::Result>>
    DownloadManager::directDownload(const Util::HarvestableItem &source, const std::string &user_agent,
                                    const DirectDownload::Operation operation, const unsigned timeout)
{
    // check if we have already delivered this URL
    if (not global_params_.force_downloads_
        and operation == DirectDownload::Operation::USE_TRANSLATION_SERVER
        and upload_tracker_.urlAlreadyDelivered(source.url_.toString()))
    {
        std::unique_ptr<DirectDownload::Result> result(new DirectDownload::Result(source, operation));
        result->response_code_ = DirectDownload::Result::SpecialResponseCodes::ITEM_ALREADY_DELIVERED;

        std::unique_ptr<Util::Future<DirectDownload::Params, DirectDownload::Result>>
                download_result(new Util::Future<DirectDownload::Params, DirectDownload::Result>(std::move(result)));
        return download_result;
    }

    // check if we have a cached response and return it immediately, if any
    auto cached_result(fetchDownloadDataFromCache(source, operation));
    if (cached_result != nullptr){
        std::unique_ptr<Util::Future<DirectDownload::Params, DirectDownload::Result>>
                download_result(new Util::Future<DirectDownload::Params, DirectDownload::Result>(std::move(cached_result)));
        return download_result;
    }

    std::unique_ptr<DirectDownload::Params> parameters(new DirectDownload::Params(source,
                                                       global_params_.translation_server_url_.toString(), user_agent,
                                                       global_params_.ignore_robots_txt_, timeout, operation));
    std::shared_ptr<DirectDownload::Tasklet> new_tasklet(new DirectDownload::Tasklet(&direct_download_tasklet_execution_counter_,
                                                         this, std::move(parameters)));

    {
        std::lock_guard<std::recursive_mutex> queue_buffer_lock(direct_download_queue_buffer_mutex_);
        direct_download_queue_buffer_.emplace_back(new_tasklet);
    }

    std::unique_ptr<Util::Future<DirectDownload::Params, DirectDownload::Result>>
        download_result(new Util::Future<DirectDownload::Params, DirectDownload::Result>(new_tasklet));
    return download_result;
}


std::unique_ptr<Util::Future<Crawling::Params, Crawling::Result>> DownloadManager::crawl(const Util::HarvestableItem &source,
                                                                                         const std::string &user_agent)
{
    std::unique_ptr<Crawling::Params> parameters(new Crawling::Params(source, user_agent, DOWNLOAD_TIMEOUT, MAX_CRAWL_TIMEOUT,
                                                 global_params_.ignore_robots_txt_, global_params_.harvestable_manager_));
    std::shared_ptr<Crawling::Tasklet> new_tasklet(new Crawling::Tasklet(&crawling_tasklet_execution_counter_,
                                                   this, std::move(parameters)));

    {
        std::lock_guard<std::recursive_mutex> queue_buffer_lock(crawling_queue_buffer_mutex_);
        crawling_queue_buffer_.emplace_back(new_tasklet);
    }

    std::unique_ptr<Util::Future<Crawling::Params, Crawling::Result>>
        download_result(new Util::Future<Crawling::Params, Crawling::Result>(new_tasklet));
    return download_result;
}


std::unique_ptr<Util::Future<RSS::Params, RSS::Result>> DownloadManager::rss(const Util::HarvestableItem &source,
                                                                             const std::string &user_agent,
                                                                             const std::string &feed_contents)
{
    std::unique_ptr<RSS::Params> parameters(new RSS::Params(source, user_agent, feed_contents, global_params_.harvestable_manager_));
    std::shared_ptr<RSS::Tasklet> new_tasklet(new RSS::Tasklet(&rss_tasklet_execution_counter_,
                                              this, std::move(parameters), upload_tracker_, global_params_.force_downloads_,
                                              global_params_.rss_feed_harvest_interval_,
                                              global_params_.force_process_rss_feeds_with_no_pub_dates_));

    {
        std::lock_guard<std::recursive_mutex> queue_buffer_lock(rss_queue_buffer_mutex_);
        rss_queue_buffer_.emplace_back(new_tasklet);
    }

    std::unique_ptr<Util::Future<RSS::Params, RSS::Result>>
        download_result(new Util::Future<RSS::Params, RSS::Result>(new_tasklet));
    return download_result;
}


void DownloadManager::addToDownloadCache(const std::string &url, const std::string &response_body, const std::string &response_header,
                                         const unsigned response_code, const std::string &error_message,
                                         const DirectDownload::Operation operation)
{
    std::lock_guard<std::recursive_mutex> download_cache_lock(cached_download_data_mutex_);

    auto cache_hit(cached_download_data_.equal_range(url));
    for (auto itr(cache_hit.first); itr != cache_hit.second; ++itr) {
        if (itr->second.operation_ == operation) {
            LOG_WARNING("cached download data overwritten for URL '" + url + "' (operation "
                        + std::to_string(static_cast<int>(operation)) + ")");

            itr->second.response_body_ = response_body;
            itr->second.response_header_ = response_header;
            itr->second.response_code_ = response_code;
            itr->second.error_message_ = error_message;
            return;
        }
    }

    cached_download_data_.insert(std::make_pair(url, CachedDownloadData { operation, response_body, response_header,
                                                                          response_code, error_message }));
}


bool DownloadManager::downloadInProgress() const {
    return direct_download_tasklet_execution_counter_ != 0 or crawling_tasklet_execution_counter_ != 0
           or rss_tasklet_execution_counter_ != 0;
}


} // end namespace Download


} // end namespace ZoteroHarvester
