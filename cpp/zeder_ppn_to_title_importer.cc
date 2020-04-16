/** \file   zeder_ppn_to_title_importer.cc
 *  \brief  Imports data from Zeder and writes a map file mapping online and print PPN's to journal titles.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *  \copyright 2018-2019 Universitätsbibliothek Tübingen.  All rights reserved.
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
#include "Compiler.h"
#include "FileUtil.h"
#include "MapUtil.h"
#include "TextUtil.h"
#include "UBTools.h"
#include "util.h"
#include "Zeder.h"


namespace {


[[noreturn]] void Usage() {
    std::cerr << "Usage: " << ::progname << " [--min-log-level=min_verbosity]\n";
    std::exit(EXIT_FAILURE);
}


void WriteMapEntry(File * const output, const std::string &key, const std::string &value) {
    if (not key.empty())
        MapUtil::WriteEntry(output, key, value);
}


void ProcessZederAndWriteMapFile(File * const map_file, const Zeder::SimpleZeder &zeder) {
    unsigned journal_count(0), bad_count(0);
    for (const auto &journal : zeder) {
        ++journal_count;

        const auto zeder_id(std::to_string(journal.getId()));
        if (unlikely(not journal.hasAttribute("tit"))) {
            ++bad_count;
            LOG_WARNING("Zeder entry #" + zeder_id + " is missing a title!");
            continue;
        }

        const auto title(TextUtil::CollapseAndTrimWhitespace(journal.lookup("tit")));
        const auto print_ppn(journal.lookup("pppn"));
        const auto online_ppn(journal.lookup("eppn"));

        if (print_ppn.empty() and online_ppn.empty()) {
            ++bad_count;
            LOG_WARNING("Zeder entry #" + zeder_id + " is missing print and online PPN's!");
            continue;
        }

        WriteMapEntry(map_file, print_ppn, zeder_id + ":print:" + title);
        WriteMapEntry(map_file, online_ppn, zeder_id + ":online:" + title);
    }

    LOG_INFO("processed " + std::to_string(journal_count) + " journal entries of which " + std::to_string(bad_count) + " was/were bad.");
}


} // unnamed namespace


int Main(int argc, char */*argv*/[]) {
    if (argc != 1)
        Usage();

    const Zeder::SimpleZeder zeder(Zeder::IXTHEO, { "eppn", "pppn", "tit" });
    if (unlikely(zeder.empty()))
        LOG_ERROR("found no Zeder entries matching any of our requested columns!"
                  " (This *should* not happen as we included the column ID!)");

    char path_template[] = "/tmp/XXXXXX";
    const int temp_fd(::mkstemp(path_template));
    if (temp_fd == -1)
        LOG_ERROR("failed to create temp file!");
    File temp_file(temp_fd);

    ProcessZederAndWriteMapFile(&temp_file, zeder);

    FileUtil::RenameFileOrDie(temp_file.getPath(), UBTools::GetTuelibPath() + "zeder_ppn_to_title.map", /* remove_target = */true);

    return EXIT_SUCCESS;
}
