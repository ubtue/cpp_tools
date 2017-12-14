/** \brief A MARC-21 utility extracts GND numbers referring to people and prints them on stdout.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2017 Universitätsbibliothek Tübingen.  All rights reserved.
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
#include <cstdlib>
#include <cstring>
#include "Compiler.h"
#include "FileUtil.h"
#include "MARC.h"
#include "StringUtil.h"
#include "util.h"


namespace {


void Usage() {
    std::cerr << "Usage: " << ::progname << " marc_authority_file\n";
    std::exit(EXIT_FAILURE);
}


bool IsPersonRecord(const MARC::Record &authority_record) {
    const auto _008(authority_record.getFirstField("008"));
    if (_008 != authority_record.end()) {
        const std::string &_008_contents(_008->getContents());
        if (_008_contents.length() > 32 and _008_contents[32] == 'a')
            return true;
    }

    return false;
}


std::string GetGNDCode(const MARC::Record &authority_record) {
    for (auto &field : authority_record.getTagRange("035")) {
        const MARC::Subfields _035_subfields(field.getContents());
        const std::string _035a_contents(_035_subfields.getFirstSubfieldWithCode('a'));
        if (StringUtil::StartsWith(_035a_contents, "(DE-588)"))
            return _035a_contents.substr(__builtin_strlen("(DE-588)"));
    }

    return "";
}

void ProcessRecords(MARC::Reader * const marc_reader) {
    unsigned total_count(0), people_gnd_count(0);
    while (const MARC::Record record = marc_reader->read()) {
        ++total_count;

        if (IsPersonRecord(record)) {
            std::cout << GetGNDCode(record) << '\n';
            ++people_gnd_count;
        }
    }

    std::cerr << "Processed a total of " << total_count << " record(s).\n";
    std::cerr << "Found " << people_gnd_count << " GND number(s) referring to people.\n";
}


} // unnamed namespace


int main(int argc, char **argv) {
    ::progname = argv[0];

    if (argc != 2)
        Usage();

    try {
        std::unique_ptr<MARC::Reader> marc_reader(MARC::Reader::Factory(argv[1]));
        ProcessRecords(marc_reader.get());
    } catch (const std::exception &x) {
        logger->error("caught exception: " + std::string(x.what()));
    }
}
