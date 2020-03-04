/** \brief Utility for replacing German BCE year references in various MARC subfields.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2020 Universitätsbibliothek Tübingen.  All rights reserved.
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

#include <utility>
#include <vector>
#include <cstdlib>
#include "MARC.h"
#include "RegexMatcher.h"
#include "util.h"


namespace {


std::vector<std::pair<RegexMatcher *, std::string>> CompileMatchers() {
    // Please note that the order in the following vector matters.  The first successful match will be used.
    const std::vector<std::pair<std::string, std::string>> patterns_and_replacements {
        { "v([0-9]+) ?- ?v([0-9]+)", "\\1 v. Chr. - \\2 v. Chr." },
        { "v([0-9]+)"              , "\\1 v. Chr."               },
    };

    std::vector<std::pair<RegexMatcher *, std::string>> compiled_patterns_and_replacements;
    for (const auto &pattern_and_replacement : patterns_and_replacements)
        compiled_patterns_and_replacements.push_back(
            std::pair<RegexMatcher *, std::string>(RegexMatcher::RegexMatcherFactoryOrDie(pattern_and_replacement.first),
                                                   pattern_and_replacement.second));
    return compiled_patterns_and_replacements;
}


const std::vector<std::pair<RegexMatcher *, std::string>> matchers_and_replacements(CompileMatchers());


// \return True if we patched at least one subfield, o/w false.
bool PatchSubfields(MARC::Record::Field * const field, const char subfield_code) {
    MARC::Subfields subfields(field->getSubfields());
    bool patched_at_least_one_subfield(false);
    for (auto &subfield : subfields) {
        if (subfield.code_ != subfield_code)
            continue;

        for (const auto &matcher_and_replacement : matchers_and_replacements) {
            RegexMatcher * const matcher(matcher_and_replacement.first);
            const std::string replaced_string(matcher->replaceWithBackreferences(subfield.value_, matcher_and_replacement.second));
            if (replaced_string != subfield.value_) {
                subfield.value_ = replaced_string;
                patched_at_least_one_subfield = true;
                break;
            }
        }
    }

    if (patched_at_least_one_subfield)
        *field = MARC::Record::Field(field->getTag(), subfields, field->getIndicator1(), field->getIndicator2());

    return patched_at_least_one_subfield;
}


const std::map<std::string, char> patch_field_to_subfield_code_map{
    { "109", 'a' },
    { "689", 'd' },
    { "SYG", 'a' },
};


// \return True if we patched at least one subfield, o/w false.
bool PatchBCEReferences(MARC::Record * const record) {
    bool patched_at_least_one_subfield(false);

    for (auto &field : *record) {
        const auto tag_and_subfield_code(patch_field_to_subfield_code_map.find(field.getTag().toString()));
        if (tag_and_subfield_code != patch_field_to_subfield_code_map.cend()
            and PatchSubfields(&field, tag_and_subfield_code->second))
            patched_at_least_one_subfield = true;
    }

    return patched_at_least_one_subfield;
}


void ProcessRecords(MARC::Reader * const marc_reader, MARC::Writer * const marc_writer) {
    unsigned record_count(0), patched_count(0);

    while (MARC::Record record = marc_reader->read()) {
        ++record_count;

        if (PatchBCEReferences(&record))
            ++patched_count;

        marc_writer->write(record);
    }

    LOG_INFO("Patched " + std::to_string(patched_count) + " of " + std::to_string(record_count) + " records.");
}


} // unnamed namespace


int Main(int argc, char *argv[]) {
    if (argc != 3)
        ::Usage("marc_input marc_output");

    auto marc_reader(MARC::Reader::Factory(argv[1]));
    auto marc_writer(MARC::Writer::Factory(argv[2]));
    ProcessRecords(marc_reader.get(), marc_writer.get());

    return EXIT_SUCCESS;
}
