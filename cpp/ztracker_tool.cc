/** \file    ztracker_tool.cc
    \brief   A utility to inspect and manipulate our Zotero tracker database.
    \author  Dr. Johannes Ruscheinski

    \copyright 2018 Universitätsbibliothek Tübingen

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Affero General Public License as
    published by the Free Software Foundation, either version 3 of the
    License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Affero General Public License for more details.

    You should have received a copy of the GNU Affero General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/
#include <iostream>
#include "TimeUtil.h"
#include "util.h"
#include "Zotero.h"


namespace {


void Usage() {
    std::cerr << "Usage: " << ::progname << " command\n"
              << "       Possible commands are:\n"
              << "       clear [url|zulu_timestamp]    => if no arguments are provided, this empties the entire database\n"
              << "                                        if a URL has been provided, just the entry with key \"url\"\n"
              << "                                        will be erased, and if a Zulu (ISO 8601) timestamp has been\n"
              << "                                        provided, all entries that are not newer are erased.\n"
              << "       insert url [error_message]    => inserts or replaces the entry for \"url\".\n"
              << "       lookup url                    => displays the timestamp and, if found, the optional message\n"
              << "                                        for this URL.\n"
              << "       list [pcre]                   => list either all entries in the database or, if the PCRE has\n"
              << "                                        been provided, ony the ones with matching URL\'s.\n"
              << "       is_present url                => prints either \"true\" or \"false\".\n\n";
    std::exit(EXIT_FAILURE);
}


void Clear(Zotero::DownloadTracker * const download_tracker, const std::string &url_or_zulu_timestamp) {
    time_t timestamp;
    std::string err_msg;

    if (url_or_zulu_timestamp.empty()) {
        std::cout << "Deleted " << download_tracker->clear() << " entries from the tracker database.\n";
    } else if (TimeUtil::Iso8601StringToTimeT(url_or_zulu_timestamp, &timestamp, &err_msg))
        std::cout << "Deleted " << download_tracker->deleteOldEntries(timestamp) << " entries from the tracker database.\n";
    else { // Assume url_or_zulu_timestamp contains a URL.
        if (download_tracker->deleteSingleEntry(url_or_zulu_timestamp))
            std::cout << "Deleted one entry from the tracker database.\n";
        else
            std::cerr << "Entry for URL \"" << url_or_zulu_timestamp << "\" could not be deleted!\n";
    }
}


void Insert(Zotero::DownloadTracker * const download_tracker, const std::string &url, const std::string &optional_message) {
    download_tracker->addOrReplace(url, optional_message, (optional_message.empty() ? "*bogus hash*" : ""));
    std::cout << "Created an entry for the URL \"" << url << "\".\n";
}


void Lookup(Zotero::DownloadTracker * const download_tracker, const std::string &url) {
    time_t timestamp;
    std::string error_message;

    if (not download_tracker->hasAlreadyBeenDownloaded(url, &timestamp, &error_message))
        std::cerr << "Entry for URL \"" << url << "\" could not be found!\n";
    else {
        if (error_message.empty())
            std::cout << url << ": " << TimeUtil::TimeTToLocalTimeString(timestamp) << '\n';
        else
            std::cout << url << ": " << TimeUtil::TimeTToLocalTimeString(timestamp) << " (" << error_message << ")\n";
    }
}


void List(Zotero::DownloadTracker * const download_tracker, const std::string &pcre) {
    std::vector<Zotero::DownloadTracker::Entry> entries;
    download_tracker->listMatches(pcre, &entries);
    
    for (const auto &entry : entries) {
        std::cout << entry.url_ << ": " << TimeUtil::TimeTToLocalTimeString(entry.creation_time_);
        if (not entry.error_message_.empty())
            std::cout << ", " << entry.error_message_;
        std::cout << '\n';
    }
}


void IsPresent(Zotero::DownloadTracker * const download_tracker, const std::string &url) {
    time_t creation_time;
    std::string error_message;
    std::cout << (download_tracker->hasAlreadyBeenDownloaded(url, &creation_time, &error_message) ? "true\n" : "false\n");
}


} // unnamed namespace


int main(int argc, char *argv[]) {
    ::progname = argv[0];

    if (argc < 2 or argc > 4)
        Usage();

    try {
        Zotero::DownloadTracker download_tracker;

        if (std::strcmp(argv[1], "clear") == 0) {
            if (argc > 3)
                LOG_ERROR("clear takes 0 or 1 arguments!");
            Clear(&download_tracker, argc == 2 ? "" : argv[2]);
        } else if (std::strcmp(argv[1], "insert") == 0) {
            if (argc < 3 or argc > 4)
                LOG_ERROR("insert takes 1 or 2 arguments!");
            Insert(&download_tracker, argv[2], argc == 3 ? "" : argv[3]);
        } else if (std::strcmp(argv[1], "lookup") == 0) {
            if (argc != 3)
                LOG_ERROR("lookup takes 1 argument!");
            Lookup(&download_tracker, argv[2]);
        } else if (std::strcmp(argv[1], "list") == 0) {
            if (argc > 3)
                LOG_ERROR("list takes 0 or 1 arguments!");
            List(&download_tracker, argc == 2 ? ".*" : argv[2]);
        } else if (std::strcmp(argv[1], "is_present") == 0) {
            if (argc != 3)
                LOG_ERROR("is_present takes 1 argument!");
            IsPresent(&download_tracker, argv[2]);
        } else
            LOG_ERROR("unknown command: \"" + std::string(argv[1]) + "\"!");
    } catch (const std::exception &x) {
        LOG_ERROR("caught exception: " + std::string(x.what()));
    }
}
