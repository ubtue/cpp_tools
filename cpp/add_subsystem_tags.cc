/** \file    add_subsystem_tags.cc
 *  \brief   Add additional tags for interfaces to identitify subset views of
             IxTheo like RelBib and Bibstudies             
 *  \author  Johannes Riedl
 */

/*
    Copyright (C) 2018, Library of the University of Tübingen

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

#include <fstream>
#include <iostream>
#include <map>
#include <vector>
#include <cstdlib>
#include "Compiler.h"
#include "File.h"
#include "MARC.h"
#include "RegexMatcher.h"
#include "StringUtil.h"
#include "util.h"

namespace {

unsigned int record_count;
unsigned int modified_count;
const std::string RELBIB_TAG("REL");
const std::string BIBSTUDIES_TAG("BIB");


[[noreturn]] void Usage() {
    std::cerr << "Usage: " << ::progname << " [--input-format=(marc-21|marc-xml)] marc_input marc_output\n";
    std::exit(EXIT_FAILURE);
}


bool HasRelBibSSGN(const MARC::Record &record) {
    for (const auto& field : record.getTagRange("084")) {
        const MARC::Subfields subfields(field.getSubfields());
        if (subfields.hasSubfieldWithValue('2', "ssgn") and subfields.hasSubfieldWithValue('a', "0"))
            return true;
    }
    return false;
}


bool HasRelBibIxTheoNotation(const MARC::Record &record) {
    // Integrate IxTheo Notations A*.B*,T*,V*,X*,Z*
    static const std::string RELBIB_IXTHEO_NOTATION_PATTERN("^[ABTVXZ][A-Z].*|.*:[ABTVXZ][A-Z].*");
    static RegexMatcher * const relbib_ixtheo_notations_matcher(RegexMatcher::RegexMatcherFactory(RELBIB_IXTHEO_NOTATION_PATTERN));
    for (const auto& field : record.getTagRange("652")) {
        for (const auto& subfieldA : field.getSubfields().extractSubfields("a")) {
            if (relbib_ixtheo_notations_matcher->matched(subfieldA))
                return true;
        }
    }
    return false;
}


bool HasRelBibExcludeDDC(const MARC::Record &record) {
    if (not record.hasTag("082"))
        return true;
    // Exclude DDC 220-289, i.e. do not include if a DDC code of this range occurs anywhere in the DDC code
    static const std::string RELBIB_EXCLUDE_DDC_RANGE_PATTERN("^2[2-8][0-9][/.]?[^.]*$");
    static RegexMatcher * const relbib_exclude_ddc_range_matcher(RegexMatcher::RegexMatcherFactory(RELBIB_EXCLUDE_DDC_RANGE_PATTERN));
    for (const auto &field : record.getTagRange("082")) {
        for (const auto &subfieldA : field.getSubfields().extractSubfields("a")) {
            if (relbib_exclude_ddc_range_matcher->matched(subfieldA))
                return true;
        }
    }
    // Exclude item if it has only DDC a 400 or 800 DDC notation
    static const std::string RELBIB_EXCLUDE_DDC_CATEGORIES_PATTERN("^[48][0-9][0-9]$");
    static RegexMatcher * const relbib_exclude_ddc_categories_matcher(RegexMatcher::RegexMatcherFactory(RELBIB_EXCLUDE_DDC_CATEGORIES_PATTERN));
    for (const auto &field : record.getTagRange("082")) {
        for (const auto &subfieldA : field.getSubfields().extractSubfields("a")) {
            if (not relbib_exclude_ddc_categories_matcher->matched(subfieldA))
                return false;
        }
    }
    return true;
}


bool MatchesRelBibDDC(const MARC::Record &record) {
    return not HasRelBibExcludeDDC(record);
}


bool IsDefinitelyRelBib(const MARC::Record &record) {
   return HasRelBibSSGN(record) or HasRelBibIxTheoNotation(record) or MatchesRelBibDDC(record);
} 


bool IsProbablyRelBib(const MARC::Record &record) {
    for (const auto& field : record.getTagRange("191")) {
        for (const auto& subfield : field.getSubfields().extractSubfields("a")) {
            if (subfield == "1")
                return true;
        }
    }
    return false;
}


std::set<std::string> GetTemporarySuperiorRelBibList() {
    const std::string relbib_superior_temporary_file("/usr/local/ub_tools/cpp/data/relbib_superior_temporary.txt");
    std::set<std::string> superior_temporary_list;
    File superior_temporary(relbib_superior_temporary_file, "r");
    std::string line;
    while (superior_temporary.getline(&line) and not superior_temporary.eof())
        superior_temporary_list.emplace(line); 
    return superior_temporary_list;
}


bool IsTemporaryRelBibSuperior(const MARC::Record &record) {
    static std::set<std::string> superior_temporary_list(GetTemporarySuperiorRelBibList());
    if (superior_temporary_list.find(record.getControlNumber()) != superior_temporary_list.end())
        return true;
    return false;
}


bool ExcludeBecauseOfRWEX(const MARC::Record &record) {
    for (const auto& field : record.getTagRange("935")) {
        for (const auto& subfield : field.getSubfields().extractSubfields("a")) {
            if (subfield == "rwex")
                return true;
        }
    }
    return false;
}


bool IsRelBibRecord(const MARC::Record &record) {
    return ((IsDefinitelyRelBib(record) or
             IsProbablyRelBib(record) or
             IsTemporaryRelBibSuperior(record)) 
             and not ExcludeBecauseOfRWEX(record));
}


bool HasBibStudiesIxTheoNotation(const MARC::Record &record) {
    static const std::string BIBSTUDIES_IXTHEO_PATTERN("^[H][A-Z].*|.*:[H][A-Z].*");
    static RegexMatcher * const relbib_ixtheo_notations_matcher(RegexMatcher::RegexMatcherFactory(BIBSTUDIES_IXTHEO_PATTERN));
    for (const auto &field : record.getTagRange("652")) {
        for (const auto &subfieldA : field.getSubfields().extractSubfields("a")) {
            if (relbib_ixtheo_notations_matcher->matched(subfieldA))
                return true;
        }
    }
    return false;
}


bool IsBibStudiesRecord(const MARC::Record &record) {
    return HasBibStudiesIxTheoNotation(record);
}


void AddSubsystemTag(MARC::Record * const record, const std::string &tag) {
    // Don't insert twice
    if (record->getFirstField(tag) != record->end())
        return;
    MARC::Subfields subfields;
    subfields.addSubfield('a', "1");
    record->insertField(tag, subfields);
}


void AddSubsystemTags(MARC::Reader * const marc_reader, MARC::Writer * const marc_writer) {
    while (MARC::Record record = marc_reader->read()) {
        ++record_count;
        bool modified_record(false);
        if (IsRelBibRecord(record)) {
            AddSubsystemTag(&record, RELBIB_TAG);
            modified_record = true;
        }
        if (IsBibStudiesRecord(record)) {
            AddSubsystemTag(&record, BIBSTUDIES_TAG);
            modified_record = true;
        }
        marc_writer->write(record);
        modified_count =  modified_record ? ++modified_count : modified_count;
    }

    std::cerr << "Modified " << modified_count << " of " << record_count << " records\n";
}

} //unnamed namespace


int main(int argc, char **argv) {
    ::progname = argv[0];

    if (argc != 3 and argc != 4)
        Usage();

    MARC::FileType reader_type(MARC::FileType::AUTO);
    if (argc == 4) {
        if (std::strcmp(argv[1], "--input-format=marc-21") == 0)
            reader_type = MARC::FileType::BINARY;
        else if (std::strcmp(argv[1], "--input-format=marc-xml") == 0)
            reader_type = MARC::FileType::XML;
        else
            Usage();
        ++argv, --argc;
    }

    const std::string marc_input_filename(argv[1]);
    const std::string marc_output_filename(argv[2]);
    if (unlikely(marc_input_filename == marc_output_filename))
        LOG_ERROR("Title data input file name equals output file name!");
    try {
        std::unique_ptr<MARC::Reader> marc_reader(MARC::Reader::Factory(marc_input_filename, reader_type));
        std::unique_ptr<MARC::Writer> marc_writer(MARC::Writer::Factory(marc_output_filename));
        AddSubsystemTags(marc_reader.get() , marc_writer.get());
    } catch (const std::exception &x) {
        LOG_ERROR("caught exception: " + std::string(x.what()));
    }
    std::cerr << "Modified " << modified_count << " of " << record_count << " records\n";

    return 0;
}
