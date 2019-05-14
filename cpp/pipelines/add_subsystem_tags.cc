/** \file    add_subsystem_tags.cc
 *  \brief   Add additional tags for interfaces to identitify subset views of
             IxTheo like RelBib and Bibstudies
 *  \author  Johannes Riedl
 *  \author  Dr. Johannes Ruscheinski
 */

/*
    Copyright (C) 2018,2019 Library of the University of Tübingen

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
#include "FileUtil.h"
#include "MARC.h"
#include "RegexMatcher.h"
#include "StringUtil.h"
#include "util.h"


namespace {


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
        for (const auto &subfield_a : field.getSubfields().extractSubfields("a")) {
            if (relbib_ixtheo_notations_matcher->matched(subfield_a))
                return true;
        }
    }
    return false;
}


bool HasPlausibleDDCPrefix(const std::string &ddc_string) {
    // Exclude records that where the entry in the DCC field is not plausible
    static const std::string PLAUSIBLE_DDC_PREFIX_PATTERN("^\\d\\d");
    static RegexMatcher * const plausible_ddc_prefix_matcher(RegexMatcher::RegexMatcherFactoryOrDie(PLAUSIBLE_DDC_PREFIX_PATTERN));
    return plausible_ddc_prefix_matcher->matched(ddc_string);
}


// Additional criteria that prevent the exclusion of a record that has a 220-289 field
bool HasAdditionalRelbibAdmissionDDC(const MARC::Record &record) {
    static const std::string RELBIB_ADMIT_DDC_PATTERN("^([12][01][0-9]|2[9][0-9]|[3-9][0-9][0-9]).*$");
    static RegexMatcher * const relbib_admit_ddc_range_matcher(RegexMatcher::RegexMatcherFactoryOrDie(RELBIB_ADMIT_DDC_PATTERN));
    for (const auto &field : record.getTagRange("082")) {
        for (const auto &subfield_a : field.getSubfields().extractSubfields("a")) {
            if (HasPlausibleDDCPrefix(subfield_a) and relbib_admit_ddc_range_matcher->matched(subfield_a))
                return true;
        }
    }
    return false;
}


bool HasRelBibExcludeDDC(const MARC::Record &record) {
    if (not record.hasTag("082"))
        return true;
    // Exclude DDC 220-289
    static const std::string RELBIB_EXCLUDE_DDC_RANGE_PATTERN("^2[2-8][0-9](/|\\.){0,2}[^.]*$");
    static RegexMatcher * const relbib_exclude_ddc_range_matcher(RegexMatcher::RegexMatcherFactoryOrDie(RELBIB_EXCLUDE_DDC_RANGE_PATTERN));

    // Make sure we have 082-fields to examine
    if (not record.hasTag("082"))
        return false;

    // In general we exclude if the exclude range is matched
    // But we include it anyway if we find another reasonable DDC-code
    for (const auto &field : record.getTagRange("082")) {
        for (const auto &subfield_a : field.getSubfields().extractSubfields("a")) {
            if (relbib_exclude_ddc_range_matcher->matched(subfield_a)) {
                if (not HasAdditionalRelbibAdmissionDDC(record))
                    return true;
            }
        }
    }

    // Exclude item if it has only a 400 or 800 DDC notation
    static const std::string RELBIB_EXCLUDE_DDC_CATEGORIES_PATTERN("^[48][0-9][0-9]$");
    static RegexMatcher * const relbib_exclude_ddc_categories_matcher(
        RegexMatcher::RegexMatcherFactoryOrDie(RELBIB_EXCLUDE_DDC_CATEGORIES_PATTERN));
    for (const auto &field : record.getTagRange("082")) {
        for (const auto &subfield_a : field.getSubfields().extractSubfields('a')) {
            if (HasPlausibleDDCPrefix(subfield_a) and not relbib_exclude_ddc_categories_matcher->matched(subfield_a))
                return false;
        }
    }
    return true;
}


inline bool MatchesRelBibDDC(const MARC::Record &record) {
    return not HasRelBibExcludeDDC(record);
}


inline bool IsDefinitelyRelBib(const MARC::Record &record) {
   return HasRelBibSSGN(record) or HasRelBibIxTheoNotation(record) or MatchesRelBibDDC(record);
}


bool IsProbablyRelBib(const MARC::Record &record) {
    for (const auto &field : record.getTagRange("191")) {
        for (const auto &subfield : field.getSubfields().extractSubfields("a")) {
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


// Tagged as not a relbib record?
bool ExcludeBecauseOfRWEX(const MARC::Record &record) {
    for (const auto &field : record.getTagRange("LOK")) {
        const auto &subfields(field.getSubfields());
        for (const auto &subfield0: subfields.extractSubfields('0')) {
            if (not StringUtil::StartsWith(subfield0, "935"))
                continue;
            for (const auto &subfield_a : subfields.extractSubfields('a')) {
                if (subfield_a == "rwex")
                    return true;
            }
        }
    }
    return false;
}


inline bool IsRelBibRecord(const MARC::Record &record) {
    return ((IsDefinitelyRelBib(record) or IsProbablyRelBib(record) or IsTemporaryRelBibSuperior(record))
            and not ExcludeBecauseOfRWEX(record));
}


// See https://github.com/ubtue/tuefind/wiki/Daten-Abzugskriterien#abzugskriterien-bibelwissenschaften for the documentation.
bool IsBibleStudiesRecord(const MARC::Record &record) {
    // 1. Abrufzeichen
    for (const auto &field : record.getTagRange("935")) {
        if (field.hasSubfieldWithValue('a', "BIIN"))
            return true;
    }

    // 2. IxTheo-Klassen
    for (const auto &field : record.getTagRange("LOK")) {
        if (field.hasSubfieldWithValue('0', "936ln")) {
            for (const auto &subfield : field.getSubfields()) {
                if (subfield.code_ == 'a' and likely(not subfield.value_.empty()) and subfield.value_[0] == 'H')
                    return true;
            }
        }
    }

    // 3. DDC Klassen
    for (const auto &field : record.getTagRange("082")) {
        if (field.getIndicator1() != ' ' or field.getIndicator2() != '0')
            continue;
        for (const auto &subfield : field.getSubfields()) {
            if (subfield.code_ == 'a' and StringUtil::StartsWith(subfield.value_, "22"))
                return true;
        }
    }

    // 4. RVK Klassen
    for (const auto &field : record.getTagRange("084")) {
        if (not field.hasSubfieldWithValue('2', "rvk"))
            continue;
        for (const auto &subfield : field.getSubfields()) {
            if (subfield.code_ == 'a' and StringUtil::StartsWith(subfield.value_, "BC"))
                return true;
        }
    }

    // 5. Basisklassifikation (BK)
    for (const auto &field : record.getTagRange("936")) {
        if (field.getIndicator1() != 'b' or field.getIndicator2() != 'k')
            continue;
        for (const auto &subfield : field.getSubfields()) {
            if (subfield.code_ == 'a'
                and (StringUtil::StartsWith(subfield.value_, "11.3") or StringUtil::StartsWith(subfield.value_, "11.4")))
                return true;
        }
    }

    // 6. Titel, die mit einem Normsatz verknüpft sind, der die GND Systematik enthält
    for (const auto &field : record.getTagRange("065")) {
        if (not field.hasSubfieldWithValue('2', "sswd"))
            continue;
        for (const auto &subfield : field.getSubfields()) {
            if (subfield.code_ == 'a' and StringUtil::StartsWith(subfield.value_, "3.2"))
                return true;
        }
    }

    // 7. SSG-Kennzeichen für den Alten Orient
    for (const auto &field : record.getTagRange("084")) {
        if (not field.hasSubfieldWithValue('2', "ssgn"))
            continue;
        for (const auto &subfield : field.getSubfields()) {
            if (subfield.code_ == 'a' and StringUtil::StartsWith(subfield.value_, "6,22"))
                return true;
        }
    }

    return false;
}


void AddSubsystemTag(MARC::Record * const record, const std::string &tag) {
    // Don't insert twice
    if (record->getFirstField(tag) != record->end())
        return;
    MARC::Subfields subfields;
    subfields.addSubfield('a', "1");
    record->insertField(tag, subfields);
}


void CollectSuperiorOrParallelWorks(const MARC::Record &record, std::unordered_set<std::string> * const superior_or_parallel_works) {
    const std::set<std::string> parallel(MARC::ExtractCrossReferencePPNs(record));
    superior_or_parallel_works->insert(parallel.begin(), parallel.end());
    superior_or_parallel_works->insert(record.getSuperiorControlNumber());
}


// See https://github.com/ubtue/tuefind/wiki/Daten-Abzugskriterien#abzugskriterien-bibelwissenschaften for the documentation.
bool IsCanonLawRecord(const MARC::Record &record) {
    // 1. Abrufzeichen
    for (const auto &field : record.getTagRange("935")) {
        if (field.hasSubfieldWithValue('a', "KALD"))
            return true;
    }

    // 2. IxTheo-Klassen
    for (const auto &field : record.getTagRange("LOK")) {
        if (field.hasSubfieldWithValue('0', "936ln")) {
            for (const auto &subfield : field.getSubfields()) {
                if (subfield.code_ == 'a' and likely(not subfield.value_.empty()) and subfield.value_[0] == 'S')
                    return true;
            }
        }
    }

    // 3. DDC Klassen
    for (const auto &field : record.getTagRange("082")) {
        if (field.getIndicator1() != ' ' or field.getIndicator2() != '0')
            continue;
        for (const auto &subfield : field.getSubfields()) {
            if (subfield.code_ == 'a'
                and (StringUtil::StartsWith(subfield.value_, "262.91") or StringUtil::StartsWith(subfield.value_, "262.92")
                     or StringUtil::StartsWith(subfield.value_, "262.93") or StringUtil::StartsWith(subfield.value_, "262.94")
                     or StringUtil::StartsWith(subfield.value_, "262.98")))
                return true;
        }
    }

    // 4. RVK Klassen
    for (const auto &field : record.getTagRange("084")) {
        if (not field.hasSubfieldWithValue('2', "rvk"))
            continue;
        for (const auto &subfield : field.getSubfields()) {
            if (subfield.code_ == 'a' and StringUtil::StartsWith(subfield.value_, "BR"))
                return true;
        }
    }

    // 5. Basisklassifikation (BK)
    for (const auto &field : record.getTagRange("936")) {
        if (field.getIndicator1() != 'b' or field.getIndicator2() != 'k')
            continue;
        for (const auto &subfield : field.getSubfields()) {
            if (subfield.code_ == 'a' and subfield.value_ == "86.97")
                return true;
        }
    }

    // 6. Titel, die mit einem Normsatz verknüpft sind, der die GND Systematik enthält
    for (const auto &field : record.getTagRange("065")) {
        if (not field.hasSubfieldWithValue('2', "sswd"))
            continue;
        for (const auto &subfield : field.getSubfields()) {
            if (subfield.code_ == 'a' and StringUtil::StartsWith(subfield.value_, "7.13"))
                return true;
        }
    }

    return false;
}


enum SubSystem { RELBIB, BIBSTUDIES, CANON_LAW };
const unsigned NUM_OF_SUBSYSTEMS(3);


// Get set of immediately belonging or superior or parallel records
void GetSubsystemPPNSet(MARC::Reader * const marc_reader, std::vector<std::unordered_set<std::string>> * const subsystem_sets) {
    while (const MARC::Record record = marc_reader->read()) {
        if (IsRelBibRecord(record)) {
            ((*subsystem_sets)[RELBIB]).emplace(record.getControlNumber());
            CollectSuperiorOrParallelWorks(record, &((*subsystem_sets)[RELBIB]));
        }
        if (IsBibleStudiesRecord(record)) {
            ((*subsystem_sets)[BIBSTUDIES]).emplace(record.getControlNumber());
            CollectSuperiorOrParallelWorks(record, &((*subsystem_sets)[BIBSTUDIES]));
        }
        if (IsCanonLawRecord(record)) {
            ((*subsystem_sets)[CANON_LAW]).emplace(record.getControlNumber());
            CollectSuperiorOrParallelWorks(record, &((*subsystem_sets)[CANON_LAW]));
        }
    }
}


const std::string RELBIB_TAG("REL");
const std::string BIBSTUDIES_TAG("BIB");
const std::string CANON_LAW_TAG("CAN");


void AddSubsystemTags(MARC::Reader * const marc_reader, MARC::Writer * const marc_writer,
                      const std::vector<std::unordered_set<std::string>> &subsystem_sets)
{
    unsigned record_count(0), modified_count(0);
    while (MARC::Record record = marc_reader->read()) {
        ++record_count;
        bool modified_record(false);
        if ((subsystem_sets[RELBIB]).find(record.getControlNumber()) != subsystem_sets[RELBIB].end()) {
            AddSubsystemTag(&record, RELBIB_TAG);
            modified_record = true;
        }
        if ((subsystem_sets[BIBSTUDIES]).find(record.getControlNumber()) != subsystem_sets[RELBIB].end()) {
            AddSubsystemTag(&record, BIBSTUDIES_TAG);
            modified_record = true;
        }
        if ((subsystem_sets[CANON_LAW]).find(record.getControlNumber()) != subsystem_sets[CANON_LAW].end()) {
            AddSubsystemTag(&record, CANON_LAW_TAG);
            modified_record = true;
        }
        if (modified_record)
            ++modified_count;
         marc_writer->write(record);
    }
    LOG_INFO("Modified " + std::to_string(modified_count) + " of " + std::to_string(record_count) + " records.");
}


void InitializeSubsystemPPNSets(std::vector<std::unordered_set<std::string>> * const subsystem_ppn_sets) {
    for (unsigned i(0); i < NUM_OF_SUBSYSTEMS; ++i)
        subsystem_ppn_sets->push_back(std::unordered_set<std::string>());
}


} //unnamed namespace


int Main(int argc, char **argv) {
    if (argc != 3)
        ::Usage("marc_input marc_output");

    const std::string marc_input_filename(argv[1]);
    const std::string marc_output_filename(argv[2]);
    if (unlikely(marc_input_filename == marc_output_filename))
        LOG_ERROR("Title data input file name equals output file name!");

    std::vector<std::unordered_set<std::string>> subsystem_sets;
    InitializeSubsystemPPNSets(&subsystem_sets);

    std::unique_ptr<MARC::Reader> marc_reader(MARC::Reader::Factory(marc_input_filename));
    GetSubsystemPPNSet(marc_reader.get(), &subsystem_sets);
    marc_reader->rewind();
    std::unique_ptr<MARC::Writer> marc_writer(MARC::Writer::Factory(marc_output_filename));
    AddSubsystemTags(marc_reader.get(), marc_writer.get(), subsystem_sets);

    return EXIT_SUCCESS;
}
