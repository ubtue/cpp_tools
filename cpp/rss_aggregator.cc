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
#include "IniFile.h"
#include "SignalUtil.h"
#include "StringUtil.h"
#include "SyndicationFormat.h"
#include "util.h"


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
    std::cerr << "Usage: " << ::progname
              << " [--verbosity=min_verbosity] [--test] xml_output_path\n"
              << "       When --test has been specified no data will be stored.\n";
    std::exit(EXIT_FAILURE);
}


// These must be in sync with the sizes in data/rss_aggregator.sql
const size_t MAX_ITEM_ID_LENGTH(100);
const size_t MAX_ITEM_URL_LENGTH(512);
const size_t MAX_SERIAL_NAME_LENGTH(200);


// \return true if the item was new, else false.
bool ProcessRSSItem(const SyndicationFormat::Item &item, const std::string &section_name, DbConnection * const db_connection) {
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

    // FIXME(ruschein):  We probably have to use an InnoDB table to guarantee atomicity here!!!
    db_connection->queryOrDie("INSERT INTO rss_aggregator SET item_id='"
                              + db_connection->escapeString(StringUtil::Truncate(MAX_ITEM_ID_LENGTH, item_id)) + "'," + "item_url='"
                              + db_connection->escapeString(StringUtil::Truncate(MAX_ITEM_URL_LENGTH, item_url))
                              + "',title_and_or_description='" + db_connection->escapeString(title_and_or_description) + ", serial_name='"
                              + db_connection->escapeString(StringUtil::Truncate(MAX_SERIAL_NAME_LENGTH, section_name)) + "'");

    return true;
}


std::unordered_map<std::string, uint64_t> section_name_to_ticks_map;


// \return the number of new items.
unsigned ProcessSection(const IniFile::Section &section, Downloader * const downloader, DbConnection * const db_connection,
                        const unsigned default_downloader_time_limit, const unsigned default_poll_interval, const uint64_t now)
{
    const std::string feed_url(section.getString("feed_url"));
    const unsigned poll_interval(section.getUnsigned("poll_interval", default_poll_interval));
    const unsigned downloader_time_limit(section.getUnsigned("downloader_time_limit", default_downloader_time_limit) * 1000);

    const std::string &section_name(section.getSectionName());
    const auto section_name_and_ticks(section_name_to_ticks_map.find(section_name));
    if (section_name_and_ticks != section_name_to_ticks_map.end()) {
        if (section_name_and_ticks->second + poll_interval < now) {
            LOG_DEBUG(section_name + ": not yet time to do work, last work was done at " + std::to_string(section_name_and_ticks->second)
                      + ".");
            return 0;
        }
    }

    unsigned new_item_count(0);
    SignalUtil::SignalBlocker sighup_blocker(SIGHUP);
    if (not downloader->newUrl(feed_url, downloader_time_limit))
        LOG_WARNING(section_name + ": failed to download the feed: " + downloader->getLastErrorMessage());
    else {
        sighup_blocker.unblock();

        std::string error_message;
        std::unique_ptr<SyndicationFormat> syndication_format(SyndicationFormat::Factory(downloader->getMessageBody(), &error_message));
        if (unlikely(syndication_format == nullptr))
            LOG_WARNING("failed to parse feed: " + error_message);
        else {
            for (const auto &item : *syndication_format) {
                SignalUtil::SignalBlocker sighup_blocker2(SIGHUP);

                if (ProcessRSSItem(item, section_name,  db_connection))
                    ++new_item_count;
            }
        }
    }

    section_name_to_ticks_map[section_name] = now;
    return new_item_count;
}


const std::string CONF_FILE_PATH("/usr/local/var/lib/tuelib/rss_aggregator.conf");


} // unnamed namespace


int Main(int argc, char *argv[]) {
    ::progname = argv[0];

    if (argc != 2 and argc != 3)
        Usage();

    bool test(false);
    if (argc == 3) {
        if (std::strcmp(argv[1], "--test") == 0) {
            test = true;
            --argc, ++argv;
        } else
            Usage();
    }

    IniFile ini_file(CONF_FILE_PATH);
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

    uint64_t ticks(0);
    Downloader downloader;
    for (;;) {
        LOG_DEBUG("now we're at " + std::to_string(ticks) + ".");

        if (sighup_seen) {
            LOG_INFO("caught SIGHUP, rereading config file...");
            ini_file.reload();
            sighup_seen = false;
        }

        const time_t before(std::time(nullptr));

        std::unordered_set<std::string> already_seen_sections;
        for (const auto &section : ini_file) {
            if (sigterm_seen) {
                LOG_INFO("caught SIGTERM, shutting down...");
                return EXIT_SUCCESS;
            }

            SignalUtil::SignalBlocker sigterm_blocker(SIGTERM);

            const std::string &section_name(section.first);
            if (not section_name.empty() and section_name != "CGI Params") {
                if (unlikely(already_seen_sections.find(section_name) != already_seen_sections.end()))
                    LOG_ERROR("duplicate section: \"" + section_name + "\"!");
                already_seen_sections.emplace(section_name);

                LOG_INFO("Processing section \"" + section_name + "\".");
                const unsigned new_item_count(ProcessSection(section.second, &downloader, &db_connection, DEFAULT_DOWNLOADER_TIME_LIMIT,
                                                             DEFAULT_POLL_INTERVAL, ticks));
                LOG_INFO("found " + std::to_string(new_item_count) + " new items.");
            }
        }

        if (test) // -> only run through our loop once
            return EXIT_SUCCESS;

        const time_t after(std::time(nullptr));

        uint64_t sleep_interval;
        if (after - before > UPDATE_INTERVAL * 60)
            sleep_interval = 0;
        else
            sleep_interval = (UPDATE_INTERVAL * 60 - (after - before));

        ::sleep(static_cast<unsigned>(sleep_interval));
        ticks += UPDATE_INTERVAL;
    }
}
