/** \file   rss_aggregator.cc
 *  \brief  Downloads and aggregates RSS feeds.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2018-2021 Universitätsbibliothek Tübingen.  All rights reserved.
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
#include <algorithm>
#include <map>
#include <unordered_map>
#include <unordered_set>
#include <cinttypes>
#include <cstring>
#include "Compiler.h"
#include "DbConnection.h"
#include "DbResultSet.h"
#include "DnsUtil.h"
#include "Downloader.h"
#include "EmailSender.h"
#include "FileUtil.h"
#include "HtmlUtil.h"
#include "IniFile.h"
#include "RegexMatcher.h"
#include "SqlUtil.h"
#include "StringUtil.h"
#include "SyndicationFormat.h"
#include "UBTools.h"
#include "util.h"
#include "VuFind.h"
#include "XmlWriter.h"


namespace {


[[noreturn]] void Usage() {
    ::Usage("[--use-web-proxy] subsystem_type email_address xml_output_path\n"
            "where subsystem_type must be one of {ixtheo,relbib,krimdok}");
}


// These must be in sync with the sizes in the vufind.rss_aggregator table!
const size_t MAX_ITEM_ID_LENGTH(768);
const size_t MAX_ITEM_URL_LENGTH(1000);
const size_t MAX_ITEM_TITLE_LENGTH(1000);
const size_t MAX_SERIAL_NAME_LENGTH(200);


struct HarvestedRSSItem {
    SyndicationFormat::Item item_;
    std::string feed_title_;
    std::string feed_url_;

    HarvestedRSSItem(const SyndicationFormat::Item item, const std::string feed_title, const std::string feed_url)
        : item_(item), feed_title_(feed_title), feed_url_(feed_url) {}
};


struct ChannelDesc {
    std::string title_;
    std::string link_;
public:
    ChannelDesc(const std::string &title, const std::string &link)
        : title_(title), link_(link) { }
};


const std::map<std::string, ChannelDesc> subsystem_type_to_channel_desc_map = {
    { "relbib",  ChannelDesc("RelBib Aggregator",  "https://relbib.de/")                },
    { "ixtheo",  ChannelDesc("IxTheo Aggregator",  "https://itheo.de/")                 },
    { "krimdok", ChannelDesc("KrimDok Aggregator", "https://krimdok.uni-tuebingen.de/") },
};


std::string GetChannelDescEntry(const std::string &subsystem_type, const std::string &entry) {
    const auto subsystem_type_and_channel_desc(subsystem_type_to_channel_desc_map.find(subsystem_type));
    if (subsystem_type_and_channel_desc == subsystem_type_to_channel_desc_map.cend())
        LOG_ERROR("unknown subsystem type \"" + subsystem_type + "\"!");

    if (entry == "title")
        return subsystem_type_and_channel_desc->second.title_;
    if (entry == "link")
        return subsystem_type_and_channel_desc->second.link_;
    LOG_ERROR("unknown entry name \"" + entry + "\"!");
}


void WriteRSSFeedXMLOutput(const std::string &subsystem_type, const std::vector<HarvestedRSSItem> &harvested_items,
                           XmlWriter * const xml_writer)
{
    xml_writer->openTag("rss", { { "version", "2.0" }, { "xmlns:tuefind", "https://github.com/ubtue/tuefind" } });
    xml_writer->openTag("channel");
    xml_writer->writeTagsWithData("title", GetChannelDescEntry(subsystem_type, "title"));
    xml_writer->writeTagsWithData("link", GetChannelDescEntry(subsystem_type, "link"));
    xml_writer->writeTagsWithData("description", "RSS Aggregator");

    for (const auto &harvested_item : harvested_items) {
        xml_writer->openTag("item");

        const auto title(harvested_item.item_.getTitle());
        if (not title.empty())
            xml_writer->writeTagsWithData("title", harvested_item.item_.getTitle());

        xml_writer->writeTagsWithData("link", harvested_item.item_.getLink());

        const auto description(HtmlUtil::ShortenText(harvested_item.item_.getDescription(), /*max_length = */500));
        if (not description.empty())
            xml_writer->writeTagsWithData("description", description);

        xml_writer->writeTagsWithData("pubDate",
                                      TimeUtil::TimeTToString(harvested_item.item_.getPubDate(), TimeUtil::RFC822_FORMAT,
                                                                     TimeUtil::UTC));
        xml_writer->writeTagsWithData("guid", harvested_item.item_.getId());
        xml_writer->writeTagsWithData("tuefind:rss_title", harvested_item.feed_title_);
        xml_writer->writeTagsWithData("tuefind:rss_url", harvested_item.feed_url_);
        xml_writer->closeTag("item", /* suppress_indent */ false);
    }

    xml_writer->closeTag("channel");
    xml_writer->closeTag("rss");
}


// \return true if the item was new, else false.
bool ProcessRSSItem(const std::string &feed_id, const SyndicationFormat::Item &item, DbConnection * const db_connection) {
    const std::string item_id(item.getId());
    db_connection->queryOrDie("SELECT insertion_time FROM tuefind_rss_items WHERE item_id='"
                              + db_connection->escapeString(item_id) + "'");
    const DbResultSet result_set(db_connection->getLastResultSet());
    if (not result_set.empty())
        return false;

    const std::string item_url(item.getLink());
    if (item_url.empty()) {
        LOG_WARNING("got an item w/o a URL, ID is \"" + item.getId() + "\"");
        return false;
    }

    db_connection->insertIntoTableOrDie("tuefind_rss_items",
                                        {
                                            { "rss_feeds_id",     StringUtil::Truncate(MAX_SERIAL_NAME_LENGTH, feed_id)        },
                                            { "item_id",          StringUtil::Truncate(MAX_ITEM_ID_LENGTH, item_id)            },
                                            { "item_url",         StringUtil::Truncate(MAX_ITEM_URL_LENGTH, item_url)          },
                                            { "item_title",       StringUtil::Truncate(MAX_ITEM_TITLE_LENGTH, item.getTitle()) },
                                            { "item_description", item.getDescription()                                        },
                                            { "pub_date",         SqlUtil::TimeTToDatetime(item.getPubDate())                  }
                                        },
                                        DbConnection::DuplicateKeyBehaviour::DKB_REPLACE);

    return true;
}


// \return the number of new items.
unsigned ProcessFeed(const std::string &feed_id, const std::string &feed_name, const std::string &feed_url,
                     const std::string &title_suppression_regex_str, const std::string &strptime_format,
                     Downloader * const downloader, DbConnection * const db_connection, const unsigned downloader_time_limit)
{
    SyndicationFormat::AugmentParams augment_params;
    augment_params.strptime_format_ = strptime_format;

    const auto title_suppression_regex(
        title_suppression_regex_str.empty() ? nullptr : RegexMatcher::RegexMatcherFactoryOrDie(title_suppression_regex_str));

    unsigned new_item_count(0);
    if (not downloader->newUrl(feed_url, downloader_time_limit))
        LOG_WARNING(feed_name + ": failed to download the feed: " + downloader->getLastErrorMessage());
    else {
        std::string error_message;
        std::unique_ptr<SyndicationFormat> syndication_format(
            SyndicationFormat::Factory(downloader->getMessageBody(), augment_params, &error_message));
        if (unlikely(syndication_format == nullptr))
            LOG_WARNING("failed to parse feed: " + error_message);
        else {
            for (const auto &item : *syndication_format) {
                if (title_suppression_regex != nullptr and title_suppression_regex->matched(item.getTitle())) {
                    LOG_INFO("Suppressed item because of title: \"" + StringUtil::ShortenText(item.getTitle(), 40) + "\".");
                    continue; // Skip suppressed item.
                }

                if (ProcessRSSItem(feed_id, item, db_connection))
                    ++new_item_count;
            }
        }
    }

    return new_item_count;
}


const unsigned HARVEST_TIME_WINDOW(60); // days


struct FeedNameAndURL {
    std::string name_;
    std::string url_;
public:
    FeedNameAndURL() = default;
    FeedNameAndURL(const FeedNameAndURL &other) = default;
    FeedNameAndURL(const std::string &name, const std::string &url)
        : name_(name), url_(url) { }
};


size_t SelectItems(const std::string &subsystem_type, DbConnection * const db_connection,
                   std::vector<HarvestedRSSItem> * const harvested_items)
{
    db_connection->queryOrDie("SELECT id,feed_name,feed_url FROM tuefind_rss_feeds WHERE FIND_IN_SET('" + subsystem_type
                              + "', subsystem_types) > 0");
    DbResultSet feeds_result_set(db_connection->getLastResultSet());
    std::unordered_map<std::string, FeedNameAndURL> feed_ids_to_names_and_urls_map;
    while (const auto row = feeds_result_set.getNextRow())
        feed_ids_to_names_and_urls_map[row["id"]] = FeedNameAndURL(row["feed_name"], row["feed_url"]);

    const std::string NOW_AS_SQL_DATETIME(SqlUtil::TimeTToDatetime(std::time(nullptr) - HARVEST_TIME_WINDOW * 86400));
    for (const auto &[feed_id, feed_name_and_url] : feed_ids_to_names_and_urls_map) {
        db_connection->queryOrDie("SELECT item_title,item_description,item_url,item_id,pub_date FROM tuefind_rss_items "
                                  "WHERE pub_date >= '" + NOW_AS_SQL_DATETIME + "' AND rss_feeds_id = "
                                  + feed_id + " ORDER BY pub_date DESC");
        DbResultSet result_set(db_connection->getLastResultSet());
        while (const DbRow row = result_set.getNextRow())
            harvested_items->emplace_back(SyndicationFormat::Item(row["item_title"], row["item_description"], row["item_url"],
                                                                  row["item_id"], SqlUtil::DatetimeToTimeT(row["pub_date"])),
                                                                  feed_name_and_url.name_, feed_name_and_url.url_);
    }

    return harvested_items->size();
}


const unsigned DEFAULT_XML_INDENT_AMOUNT(2);


int ProcessFeeds(const std::string &subsystem_type, const std::string &xml_output_filename,
                 DbConnection * const db_connection, Downloader * const downloader)
{
    db_connection->queryOrDie("SELECT * FROM tuefind_rss_feeds WHERE subsystem_types LIKE '%" + subsystem_type + "%'");
    auto result_set(db_connection->getLastResultSet());
    while (const auto row = result_set.getNextRow()) {
        LOG_INFO("Processing feed \"" + row["feed_name"] + "\".");
        const unsigned new_item_count(ProcessFeed(row["id"], row["feed_name"], row["feed_url"],
                                                  row.getValue("title_suppression_regex"),
                                                  row.getValue("strptime_format"), downloader, db_connection,
                                                  StringUtil::ToUnsigned(row["downloader_time_limit"])));
        LOG_INFO("Downloaded " + std::to_string(new_item_count) + " new items.");
    }

    std::vector<HarvestedRSSItem> harvested_items;
    const auto feed_item_count(SelectItems(subsystem_type, db_connection, &harvested_items));

    // scoped here so that we flush and close the output file right away
    {
        XmlWriter xml_writer(FileUtil::OpenOutputFileOrDie(xml_output_filename).release(),
                             XmlWriter::WriteTheXmlDeclaration, DEFAULT_XML_INDENT_AMOUNT);
        WriteRSSFeedXMLOutput(subsystem_type, harvested_items, &xml_writer);
    }
    LOG_INFO("Created our feed with " + std::to_string(feed_item_count) + " items from the last "
             + std::to_string(HARVEST_TIME_WINDOW) + " days.");

    return EXIT_SUCCESS;
}


} // unnamed namespace


int Main(int argc, char *argv[]) {
    if (argc != 4 and argc != 5)
        Usage();

    Downloader::Params params;
    if (argc == 5) {
        if (std::strcmp(argv[0], "--use-web-proxy") != 0)
            Usage();
        --argc, ++argv;
        params.proxy_host_and_port_ = UBTools::GetUBWebProxyURL();
    }
    Downloader downloader(params);

    const std::string subsystem_type(argv[1]);
    if (subsystem_type != "ixtheo" and subsystem_type != "relbib" and subsystem_type != "krimdok")
        LOG_ERROR("subsystem_type must be one of {ixtheo,relbib,krimdok}!");

    const std::string email_address(argv[2]);
    const std::string xml_output_filename(argv[3]);

    const auto db_connection(VuFind::GetDbConnection());

    try {
        return ProcessFeeds(subsystem_type, xml_output_filename, db_connection.get(), &downloader);
    } catch (const std::runtime_error &x) {
        const auto program_basename(FileUtil::GetBasename(::progname));
        const auto subject(program_basename + " failed on " + DnsUtil::GetHostname()
                           + " (subsystem_type: " + subsystem_type + ")");
        const auto message_body("caught exception: " + std::string(x.what()));
        if (EmailSender::SimplerSendEmail("no_reply@ub.uni-tuebingen.de", { email_address }, subject, message_body,
                                          EmailSender::VERY_HIGH) < 299)
            return EXIT_FAILURE;
        else
            LOG_ERROR("failed to send an email error report!");
    }
}
