/** \file   rss_aggregator.cc
 *  \brief  Downloads and aggregates RSS feeds.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2018 Universitätsbibliothek Tübingen.  All rights reserved.
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
#include <iostream>
#include <unordered_map>
#include <unordered_set>
#include <cinttypes>
#include <csignal>
#include <cstring>
#include <unistd.h>
#include "Compiler.h"
#include "DbConnection.h"
#include "DbResultSet.h"
#include "Downloader.h"
#include "FileUtil.h"
#include "IniFile.h"
#include "SignalUtil.h"
#include "StringUtil.h"
#include "SyndicationFormat.h"
#include "UBTools.h"
#include "util.h"
#include "XmlWriter.h"


namespace {


volatile sig_atomic_t sigterm_seen = false;


void SigTermHandler(int /* signum */) {
    sigterm_seen = true;
}


volatile sig_atomic_t sighup_seen = false;


void SigHupHandler(int /* signum */) {
    sighup_seen = true;
}


[[noreturn]] void Usage() {
    ::Usage("[--test] [--sort-by-date] [--strptime-format=format] [--config-file=config_file_path] xml_output_path\n"
            "       When --test has been specified no data will be stored.\n"
            "       The default config file path is \"" + UBTools::GetTuelibPath() + FileUtil::GetBasename(::progname) + ".conf\".");
}


// These must be in sync with the sizes in data/ub_tools.sql (rss_aggregator table)
const size_t MAX_ITEM_ID_LENGTH(100);
const size_t MAX_ITEM_URL_LENGTH(512);
const size_t MAX_SERIAL_NAME_LENGTH(200);


struct HarvestedRSSItem {
    SyndicationFormat::Item item_;
    std::string item_id_;
    std::string feed_title_;
    std::string feed_url_;

    HarvestedRSSItem(const SyndicationFormat::Item item, const std::string item_id, const std::string feed_title, const std::string feed_url)
        : item_(item), item_id_(item_id), feed_title_(feed_title), feed_url_(feed_url) {}
};


void WriteRSSFeedXMLOutput(const bool sort_by_date, const IniFile &ini_file, std::vector<HarvestedRSSItem> * const harvested_items,
                           XmlWriter * const xml_writer)
{
    if (sort_by_date) {
        std::sort(harvested_items->begin(), harvested_items->end(), [](const HarvestedRSSItem &a, const HarvestedRSSItem &b) {
            return a.item_.getPubDate() > b.item_.getPubDate();
        });
    }

    xml_writer->openTag("rss", { { "version", "2.0" }, { "xmlns:tuefind", "https://github.com/ubtue/tuefind" } });
    xml_writer->openTag("channel");
    xml_writer->writeTagsWithEscapedData("title", ini_file.getString("Channel", "title"));
    xml_writer->writeTagsWithEscapedData("link", ini_file.getString("Channel", "link"));
    xml_writer->writeTagsWithEscapedData("description", ini_file.getString("Channel", "description"));

    for (const auto &harvested_item : *harvested_items) {
        const auto description(harvested_item.item_.getDescription().empty() ? harvested_item.item_.getTitle()
                                                                             : harvested_item.item_.getDescription());

        xml_writer->openTag("item");
        xml_writer->writeTagsWithEscapedData("title", harvested_item.item_.getTitle());
        xml_writer->writeTagsWithEscapedData("link", harvested_item.item_.getLink());
        xml_writer->writeTagsWithEscapedData("description", description);
        xml_writer->writeTagsWithEscapedData("pubDate",
                                             TimeUtil::TimeTToString(harvested_item.item_.getPubDate(), TimeUtil::RFC822_FORMAT,
                                                                     TimeUtil::UTC));
        xml_writer->writeTagsWithEscapedData("guid", harvested_item.item_id_);
        xml_writer->writeTagsWithEscapedData("tuefind:rss_title", harvested_item.feed_title_);
        xml_writer->writeTagsWithEscapedData("tuefind:rss_url", harvested_item.feed_url_);
        xml_writer->closeTag("item", /* suppress_indent */ false);
    }

    xml_writer->closeTag("channel");
    xml_writer->closeTag("rss");
}


// \return true if the item was new, else false.
bool ProcessRSSItem(const bool test, std::vector<HarvestedRSSItem> * const harvested_items, const SyndicationFormat::Item &item,
                    const std::string &section_name, const std::string &feed_url, DbConnection * const db_connection)
{
    const std::string item_id(item.getId());
    db_connection->queryOrDie("SELECT insertion_time FROM rss_aggregator WHERE item_id='" + db_connection->escapeString(item_id) + "'");
    const DbResultSet result_set(db_connection->getLastResultSet());
    if (not result_set.empty())
        return false;

    const std::string item_url(item.getLink());
    if (item_url.empty()) {
        LOG_WARNING("got an item w/o a URL, ID is \"" + item.getId());
        return false;
    }

    std::string title_and_or_description(item.getTitle());
    if (title_and_or_description.empty())
        title_and_or_description = item.getDescription();
    else {
        const std::string description(item.getDescription());
        if (not description.empty())
            title_and_or_description += " (" + description + ")";
    }

    harvested_items->emplace_back(item, item_id, section_name, feed_url);

    if (not test)
        db_connection->insertIntoTableOrDie("rss_aggregator",
                                            {
                                                { "item_id",                  StringUtil::Truncate(MAX_ITEM_ID_LENGTH, item_id)          },
                                                { "item_url",                 StringUtil::Truncate(MAX_ITEM_URL_LENGTH, item_url)        },
                                                { "title_and_or_description", title_and_or_description                                   },
                                                { "serial_name",              StringUtil::Truncate(MAX_SERIAL_NAME_LENGTH, section_name) }
                                            });

    return true;
}


void CheckForSigTermAndExitIfSeen() {
    if (sigterm_seen) {
        LOG_WARNING("caught SIGTERM, exiting...");
        std::exit(EXIT_SUCCESS);
    }
}


void CheckForSigHupAndReloadIniFileIfSeen(IniFile * const ini_file) {
    if (sighup_seen) {
        LOG_INFO("caught SIGHUP, reloading config file...");
        ini_file->reload();
        sighup_seen = false;
    }
}


std::unordered_map<std::string, uint64_t> section_name_to_ticks_map;


// \return the number of new items.
unsigned ProcessSection(const bool test, std::vector<HarvestedRSSItem> * const harvested_items, const IniFile::Section &section,
                        const SyndicationFormat::AugmentParams &augment_params, Downloader * const downloader,
                        DbConnection * const db_connection, const unsigned default_downloader_time_limit,
                        const unsigned default_poll_interval, const uint64_t now)
{
    const std::string feed_url(section.getString("feed_url"));
    const unsigned poll_interval(section.getUnsigned("poll_interval", default_poll_interval));
    const unsigned downloader_time_limit(section.getUnsigned("downloader_time_limit", default_downloader_time_limit) * 1000);
    const std::string &section_name(section.getSectionName());

    if (test) {
        std::cout << "Processing section \"" << section_name << "\":\n"
                  << "\tfeed_url: " << feed_url << '\n'
                  << "\tpoll_interval: " << poll_interval << " (ignored)\n"
                  << "\tdownloader_time_limit: " << downloader_time_limit << "\n\n";
    }

    const auto section_name_and_ticks(section_name_to_ticks_map.find(section_name));
    if (section_name_and_ticks != section_name_to_ticks_map.end()) {
        if (section_name_and_ticks->second + poll_interval < now) {
            LOG_DEBUG(section_name + ": not yet time to do work, last work was done at " + std::to_string(section_name_and_ticks->second)
                      + ".");
            if (not test)
                return 0;
        }
    }

    unsigned new_item_count(0);
    SignalUtil::SignalBlocker sigterm_blocker(SIGTERM);
    if (not downloader->newUrl(feed_url, downloader_time_limit))
        LOG_WARNING(section_name + ": failed to download the feed: " + downloader->getLastErrorMessage());
    else {
        sigterm_blocker.unblock();
        if (not test)
            CheckForSigTermAndExitIfSeen();

        std::string error_message;
        std::unique_ptr<SyndicationFormat> syndication_format(
            SyndicationFormat::Factory(downloader->getMessageBody(), augment_params, &error_message));
        if (unlikely(syndication_format == nullptr))
            LOG_WARNING("failed to parse feed: " + error_message);
        else {
            for (const auto &item : *syndication_format) {
                if (not test)
                    CheckForSigTermAndExitIfSeen();
                SignalUtil::SignalBlocker sigterm_blocker2(SIGTERM);

                if (ProcessRSSItem(test, harvested_items, item, section_name, feed_url, db_connection))
                    ++new_item_count;
            }
        }
    }

    section_name_to_ticks_map[section_name] = now;
    return new_item_count;
}


const unsigned DEFAULT_XML_INDENT_AMOUNT(2);


} // unnamed namespace


int Main(int argc, char *argv[]) {
    if (argc < 2)
        Usage();

    bool test(false);
    if (std::strcmp(argv[1], "--test") == 0) {
        test = true;
        --argc, ++argv;
    }

    bool sort_by_date(false);
    if (std::strcmp(argv[1], "--sort-by-date") == 0) {
        sort_by_date = true;
        --argc, ++argv;
    }

    SyndicationFormat::AugmentParams augment_params;
    if (std::strcmp(argv[1], "--strptime-format=") == 0) {
        augment_params.strptime_format_ = argv[1] + __builtin_strlen("--strptime-format=");
        --argc, ++argv;
    }

    std::string config_file_path(UBTools::GetTuelibPath() + FileUtil::GetBasename(::progname) + ".conf");
    if (StringUtil::StartsWith(argv[1], "--config-file=")) {
        config_file_path = argv[1] + __builtin_strlen("--config-file=");
        --argc, ++argv;
    }

    if (argc != 2)
        Usage();

    IniFile ini_file;
    DbConnection db_connection(ini_file);

    const unsigned DEFAULT_POLL_INTERVAL(ini_file.getUnsigned("", "default_poll_interval"));
    const unsigned DEFAULT_DOWNLOADER_TIME_LIMIT(ini_file.getUnsigned("", "default_downloader_time_limit"));
    const unsigned UPDATE_INTERVAL(ini_file.getUnsigned("", "update_interval"));

    if (not test) {
        SignalUtil::InstallHandler(SIGTERM, SigTermHandler);
        SignalUtil::InstallHandler(SIGHUP, SigHupHandler);

        if (::daemon(0, 1 /* do not close file descriptors and redirect to /dev/null */) != 0)
            LOG_ERROR("we failed to deamonize our process!");
    }

    const std::string xml_output_filename(argv[1]);
    std::vector<HarvestedRSSItem> harvested_items;

    uint64_t ticks(0);
    Downloader downloader;
    for (;;) {
        LOG_DEBUG("now we're at " + std::to_string(ticks) + ".");

        CheckForSigHupAndReloadIniFileIfSeen(&ini_file);
        harvested_items.clear();

        const time_t before(std::time(nullptr));

        std::unordered_set<std::string> already_seen_sections;
        for (const auto &section : ini_file) {
            if (sigterm_seen) {
                LOG_INFO("caught SIGTERM, shutting down...");
                return EXIT_SUCCESS;
            }

            SignalUtil::SignalBlocker sighup_blocker(SIGHUP);

            const std::string &section_name(section.getSectionName());
            if (not section_name.empty() and section_name != "CGI Params" and section_name != "Database" and section_name != "Channel") {
                if (unlikely(already_seen_sections.find(section_name) != already_seen_sections.end()))
                    LOG_ERROR("duplicate section: \"" + section_name + "\"!");
                already_seen_sections.emplace(section_name);

                LOG_INFO("Processing section \"" + section_name + "\".");
                const unsigned new_item_count(ProcessSection(test, &harvested_items, section, augment_params, &downloader, &db_connection,
                                                             DEFAULT_DOWNLOADER_TIME_LIMIT, DEFAULT_POLL_INTERVAL, ticks));
                LOG_INFO("found " + std::to_string(new_item_count) + " new items.");
            }
        }

        // scoped here so that we flush and close the output file right away
        {
            XmlWriter xml_writer(FileUtil::OpenOutputFileOrDie(xml_output_filename).release(),
                                XmlWriter::WriteTheXmlDeclaration, DEFAULT_XML_INDENT_AMOUNT);
            WriteRSSFeedXMLOutput(sort_by_date, ini_file, &harvested_items, &xml_writer);
        }

        if (test) // -> only run through our loop once
            return EXIT_SUCCESS;

        const time_t after(std::time(nullptr));

        uint64_t sleep_interval;
        if (after - before > UPDATE_INTERVAL * 60)
            sleep_interval = 0;
        else
            sleep_interval = (UPDATE_INTERVAL * 60 - (after - before));

        unsigned total_time_slept(0);
        do {
            const unsigned actual_time_slept(::sleep(static_cast<unsigned>(sleep_interval - total_time_slept)));
            CheckForSigTermAndExitIfSeen();
            CheckForSigHupAndReloadIniFileIfSeen(&ini_file);

            total_time_slept += actual_time_slept;
        } while (total_time_slept < sleep_interval);
        ticks += UPDATE_INTERVAL;
    }
}
