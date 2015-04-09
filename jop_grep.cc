/** \file job_grep.cc
 *  \brief jop_grep is a command-line utility for the extration of JOP-relevant field and subfield values from
 *         MARC-21 records.
 *
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2015 Universitätsbiblothek Tübingen.  All rights reserved.
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
#include <fstream>
#include <iostream>
#include <memory>
#include <unordered_set>
#include <climits>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <getopt.h>
#include "DirectoryEntry.h"
#include "Leader.h"
#include "MarcUtil.h"
#include "RegexMatcher.h"
#include "StringUtil.h"
#include "Subfields.h"
#include "util.h"


void Usage() {
    std::cerr << "Usage: " << progname << " input_filename [optional_max_result_count]\n";
    std::exit(EXIT_FAILURE);
}


void JOP_Grep(const std::string &input_filename, const unsigned max_result_count) {
    FILE *input = std::fopen(input_filename.c_str(), "rb");
    if (input == NULL)
	Error("can't open \"" + input_filename + "\" for reading!");

    Leader *raw_leader;
    std::vector<DirectoryEntry> dir_entries;
    std::vector<std::string> field_data;
    std::string err_msg;
    unsigned count(0), result_count(0);

    while (MarcUtil::ReadNextRecord(input, &raw_leader, &dir_entries, &field_data, &err_msg)) {
	++count;
	std::unique_ptr<Leader> leader(raw_leader);
	const bool is_article(leader->isArticle());
	const bool is_serial(leader->isSerial());
	if (not is_article and not is_serial)
	    continue;

	std::string control_number, isbn, issn;
	for (unsigned i(0); i < dir_entries.size(); ++i) {
	    const std::string tag(dir_entries[i].getTag());
	    if (tag == "001")
		control_number = field_data[i];
	    else if (tag == "020" or tag == "022") {
		const Subfields subfields(field_data[i]);
		auto begin_end = subfields.getIterators('a');
		if (begin_end.first != begin_end.second) {
		    if (tag == "020")
			isbn = begin_end.first->second;
		    else // Assume tag == "022".
			issn = begin_end.first->second;
		}
	    } else if (is_article and tag == "773") {
		const Subfields subfields(field_data[i]);
		auto begin_end = subfields.getIterators('x'); // ISSN
		if (begin_end.first != begin_end.second)
		    issn = begin_end.first->second;
		begin_end = subfields.getIterators('z'); // ISBN
		if (begin_end.first != begin_end.second)
		    isbn = begin_end.first->second;
	    }
	    
	    if (not issn.empty() or not isbn.empty()) {
		++result_count;
		if (result_count > max_result_count)
		    goto done;
		break;
	    }
	}

	if (not issn.empty())
	    std::cout << (is_serial ? "journal" : "article") << ", ISSN: " << issn << '\n';
	else if (not isbn.empty())
	    std::cout << (is_serial ? "journal" : "article") << ", ISBN: " << isbn << '\n';
    }

    if (not err_msg.empty())
	Error(err_msg);

done:
    std::cerr << "Matched " << result_count << " records of " << count << " overall records.\n";

    std::fclose(input);
}


int main(int argc, char **argv) {
    progname = argv[0];

    if (argc != 2 and argc != 3)
	Usage();

    unsigned max_result_count(UINT_MAX);
    if (argc == 3) {
	if (not StringUtil::ToUnsigned(argv[2], &max_result_count) or max_result_count == 0)
	    Usage();
    }

    JOP_Grep(argv[1], max_result_count);
}
