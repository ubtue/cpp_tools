/** \file    add_author_synonyms.cc
 *  \brief   Adds author synonyms to each record.
 *  \author  Oliver Obenland
 */

/*
    Copyright (C) 2016-2018, Library of the University of Tübingen

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
#include <map>
#include <vector>
#include <cstdlib>
#include "Compiler.h"
#include "MARC.h"
#include "StringUtil.h"
#include "util.h"


static unsigned modified_count(0);
static unsigned record_count(0);


namespace {

[[noreturn]] void Usage() {
    std::cerr << "Usage: " << ::progname << " master_marc_input norm_data_marc_input marc_output\n";
    std::exit(EXIT_FAILURE);
}


void RemoveCommasDuplicatesAndEmptyEntries(std::vector<std::string> * const vector) {
    std::vector<std::string> cleaned_up_vector;
    std::set<std::string> unique_entries;

    for (auto &entry : *vector) {
        StringUtil::RemoveChars(",", &entry);

        if (entry.empty())
            continue;

        const bool is_new_entry(unique_entries.emplace(entry).second);
        if (is_new_entry)
            cleaned_up_vector.emplace_back(std::move(entry));
    }
    vector->swap(cleaned_up_vector);
}


std::string ExtractNameFromSubfields(const MARC::Record::Field &field, const std::string &subfield_codes) {
    auto subfield_values(field.getSubfields().extractSubfields(subfield_codes));

    if (subfield_values.empty())
        return "";

    std::sort(subfield_values.begin(), subfield_values.end());
    return StringUtil::Join(subfield_values, ' ');
}


void ExtractSynonyms(MARC::Reader * const marc_reader, std::map<std::string, std::string> &author_to_synonyms_map,
                     const std::string &field_list)
{
    std::set<std::string> synonyms;
    std::vector<std::string> tags_and_subfield_codes;
    if (unlikely(StringUtil::Split(field_list, ':', &tags_and_subfield_codes) < 2))
        LOG_ERROR("need at least two fields!");
    unsigned count(0);
    while (const MARC::Record record = marc_reader->read()) {
        ++count;

        const auto primary_name_field(record.findTag(tags_and_subfield_codes[0].substr(0, MARC::Record::TAG_LENGTH)));
        if (primary_name_field == record.end())
            continue;

        const std::string primary_name(ExtractNameFromSubfields(*primary_name_field,
                                                                tags_and_subfield_codes[0].substr(3)));
        if (unlikely(primary_name.empty()))
            continue;

        std::vector<std::string> alternatives;
        alternatives.emplace_back(primary_name);
        if (author_to_synonyms_map.find(primary_name) != author_to_synonyms_map.end())
            continue;

        for (unsigned i(1); i < tags_and_subfield_codes.size(); ++i) {
            const std::string tag(tags_and_subfield_codes[i].substr(0, 3));
            const std::string secondary_field_subfield_codes(tags_and_subfield_codes[i].substr(3));
            for (auto secondary_name_field(record.findTag(tag));
                secondary_name_field != record.end();
                ++secondary_name_field)
            {
                const std::string secondary_name(ExtractNameFromSubfields(*secondary_name_field,
                                                                          secondary_field_subfield_codes));
                if (not secondary_name.empty())
                    alternatives.emplace_back(secondary_name);
            }
        }
        RemoveCommasDuplicatesAndEmptyEntries(&alternatives);
        if (alternatives.size() <= 1)
            continue;

        alternatives.erase(alternatives.begin());
        author_to_synonyms_map.emplace(primary_name, StringUtil::Join(alternatives, ','));
    }

    std::cout << "Found synonyms for " << author_to_synonyms_map.size() << " authors while processing " << count
              << " norm data records.\n";
}


const std::string SYNOMYM_FIELD("109"); // This must be an o/w unused field!


void ProcessRecord(MARC::Record * const record, const std::map<std::string, std::string> &author_to_synonyms_map,
                   const std::string &primary_author_field)
{
    if (unlikely(record->findTag(SYNOMYM_FIELD) != record->end()))
        LOG_ERROR("field " + SYNOMYM_FIELD + " is apparently already in use in at least some title records!");

    const auto primary_name_field(record->findTag(primary_author_field.substr(0, 3)));
    if (primary_name_field == record->end())
        return;

    const std::string primary_name(ExtractNameFromSubfields(*primary_name_field,
                                                            primary_author_field.substr(3)));
    if (unlikely(primary_name.empty()))
        return;

    const auto synonyms_iterator = author_to_synonyms_map.find(primary_name);
    if (synonyms_iterator == author_to_synonyms_map.end())
        return;

    const std::string synonyms = synonyms_iterator->second;
    MARC::Subfields subfields;
    subfields.addSubfield('a', synonyms);

    if (not record->insertField(SYNOMYM_FIELD, subfields)) {
        LOG_WARNING("Not enough room to add a " + SYNOMYM_FIELD + " field! (Control number: "
                    + record->getControlNumber() + ")");
        return;
    }
    ++modified_count;
}


void AddAuthorSynonyms(MARC::Reader * const marc_reader, MARC::Writer * marc_writer,
                       const std::map<std::string, std::string> &author_to_synonyms_map,
                       const std::string &primary_author_field)
{
    while (MARC::Record record = marc_reader->read()) {
        ProcessRecord(&record, author_to_synonyms_map, primary_author_field);
        marc_writer->write(record);
        ++record_count;
    }

    std::cerr << "Modified " << modified_count << " of " << record_count << " record(s).\n";
}


} // unnamed namespace


int Main(int argc, char **argv) {
    if (argc != 4)
        Usage();

    const std::string marc_input_filename(argv[1]);
    const std::string authority_data_marc_input_filename(argv[2]);
    const std::string marc_output_filename(argv[3]);

    if (unlikely(marc_input_filename == marc_output_filename))
        LOG_ERROR("Title input file name equals title output file name!");
    if (unlikely(authority_data_marc_input_filename == marc_output_filename))
        LOG_ERROR("Authority data input file name equals MARC output file name!");

    auto marc_reader(MARC::Reader::Factory(marc_input_filename));
    auto authority_reader(MARC::Reader::Factory(authority_data_marc_input_filename));
    auto marc_writer(MARC::Writer::Factory(marc_output_filename));

    try {
        std::map<std::string, std::string> author_to_synonyms_map;
        ExtractSynonyms(authority_reader.get(), author_to_synonyms_map, "100abcd:400abcd");
        AddAuthorSynonyms(marc_reader.get(), marc_writer.get(), author_to_synonyms_map, "100abcd");
    } catch (const std::exception &x) {
        LOG_ERROR("caught exception: " + std::string(x.what()));
    }

    return EXIT_SUCCESS;
}
