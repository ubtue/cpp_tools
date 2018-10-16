/** \file    create_match_db.cc
 *  \brief   Creates mapping databases from normalised author names and titles to control numbers.
 *  \author  Dr. Johannes Ruscheinski
 *
 *  Copyright (C) 2018, Library of the University of Tübingen
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
#include <set>
#include <unordered_set>
#include <cctype>
#include <cstdlib>
#include "BSZUtil.h"
#include "Compiler.h"
#include "ControlNumberGuesser.h"
#include "MARC.h"
#include "util.h"


namespace {


[[noreturn]] void Usage() {
    std::cerr << "Usage: " << ::progname << " [--min-log-level=min_verbosity] marc_titles\n";
    std::exit(EXIT_FAILURE);
}


void PopulateTables(ControlNumberGuesser * const control_number_guesser, MARC::Reader * const reader) {
    unsigned processed_record_count(0), records_with_empty_titles(0);
    while (const auto record = reader->read()) {
        ++processed_record_count;
        const auto control_number(record.getControlNumber());

        std::set<std::string> author_names(record.getAllAuthors());
        control_number_guesser->insertAuthors(author_names, control_number);

        const auto title(record.getCompleteTitle());
        if (unlikely(title.empty())) {
            ++records_with_empty_titles;
            LOG_DEBUG("Empty title in record w/ control number: " + control_number);
        } else
            control_number_guesser->insertTitle(title, control_number);

        std::string year, volume, issue;
        BSZUtil::ExtractYearVolumeIssue(record, &year, &volume, &issue);
        if (not year.empty())
            control_number_guesser->insertYear(year, control_number);
    }

    LOG_INFO("Processed " + std::to_string(processed_record_count) + " records.");
    LOG_INFO("Found " + std::to_string(records_with_empty_titles) + " records with empty titles.");
}


} // unnamed namespace


int Main(int argc, char **argv) {
    if (argc != 2)
        Usage();

    ControlNumberGuesser control_number_guesser(ControlNumberGuesser::CLEAR_DATABASES);
    auto reader(MARC::Reader::Factory(argv[1]));
    PopulateTables(&control_number_guesser, reader.get());

    return EXIT_SUCCESS;
}
