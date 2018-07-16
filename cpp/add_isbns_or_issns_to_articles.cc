/** \file    add_isbns_or_issns_to_articles.cc
 *  \brief   A tool for adding missing ISBN's (field 020$a) or ISSN's (field 773$x)to articles entries,
 *           in MARC-21 data.
 *  \author  Dr. Johannes Ruscheinski
 */

/*
    Copyright (C) 2015-2018, Library of the University of Tübingen

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
#include <memory>
#include <unordered_map>
#include <cstdlib>
#include <cstring>
#include "MARC.h"
#include "MiscUtil.h"
#include "StringUtil.h"
#include "util.h"


namespace {


[[noreturn]] void Usage() {
    std::cerr << "Usage: " << progname << " master_marc_input marc_output\n";
    std::cerr << "  Adds host/parent/journal ISBNs and ISSNs to article entries found in the\n";
    std::cerr << "  master_marc_input and writes this augmented file as marc_output.  The ISBNs and ISSNs are\n";
    std::cerr << "  extracted from superior entries found in master_marc_input.\n";
    std::exit(EXIT_FAILURE);
}


void PopulateParentIdToISBNAndISSNMap(
    MARC::Reader * const marc_reader,
    std::unordered_map<std::string, std::string> * const parent_id_to_isbn_and_issn_map)
{
    LOG_INFO("Starting extraction of ISBN's and ISSN's.");

    unsigned count(0), extracted_isbn_count(0), extracted_issn_count(0);
    std::string err_msg;
    while (const MARC::Record record = marc_reader->read()) {
        ++count;

        if (not record.isSerial() and not record.isMonograph())
            continue;

        // Try to see if we have an ISBN:
        const auto field_020(record.findTag("020"));
        if (field_020 != record.end()) {
            const std::string isbn(field_020->getFirstSubfieldWithCode('a'));
            if (not isbn.empty()) {
                (*parent_id_to_isbn_and_issn_map)[record.getControlNumber()] = isbn;
                ++extracted_isbn_count;
                continue;
            }
        } else
            continue;

        std::string issn;
        // 1. First try to get an ISSN from 029$a, (according to the BSZ's PICA-to-MARC mapping
        // documentation this contains the "authorised" ISSN) but only if the indicators are correct:
        for (const auto &_029_field : record.getTagRange("029")) {
            const auto subfields(_029_field.getSubfields());

            // We only want fields with indicators 'x' and 'a':
            if (_029_field.getIndicator1() != 'x' or _029_field.getIndicator2() != 'a')
                continue;

            issn = subfields.getFirstSubfieldWithCode('a');
            if (not issn.empty()) {
                (*parent_id_to_isbn_and_issn_map)[record.getControlNumber()] = issn;
                ++extracted_issn_count;
            }
        }

        // 2. If we don't already have an ISSN check 022$a as a last resort:
        if (issn.empty()) {
            const auto field_022(record.findTag("022"));
            if (field_022 != record.end()) {
                issn = field_022->getFirstSubfieldWithCode('a');
                if (not issn.empty()) {
                    (*parent_id_to_isbn_and_issn_map)[record.getControlNumber()] = issn;
                    ++extracted_issn_count;
                }
            }
        }
    }

    if (not err_msg.empty())
        LOG_ERROR(err_msg);

    LOG_INFO("Read " + std::to_string(count) + " records.");
    LOG_INFO("Extracted " + std::to_string(extracted_isbn_count) + " ISBNs.");
    LOG_INFO("Extracted " + std::to_string(extracted_issn_count) + " ISSNs.");
}


void AddMissingISBNsOrISSNsToArticleEntries(MARC::Reader * const marc_reader,
                                            MARC::Writer * const marc_writer, const std::unordered_map<std::string,
                                            std::string> &parent_id_to_isbn_and_issn_map)
{
    LOG_INFO("Starting augmentation of article entries.");

    unsigned count(0), isbns_added(0), issns_added(0), missing_host_record_ctrl_num_count(0),
             missing_isbn_or_issn_count(0);
    while (MARC::Record record = marc_reader->read()) {
        ++count;

        if (not record.isArticle()) {
            marc_writer->write(record);
            continue;
        }

        const auto _773_field(record.findTag("773"));
        if (_773_field == record.end()) {
            marc_writer->write(record);
            continue;
        }

        auto subfields(_773_field->getSubfields());
        if (subfields.hasSubfield('x')) {
            marc_writer->write(record);
            continue;
        }

        if (not subfields.hasSubfield('w')) {       // Record control number of Host Item Entry.
            marc_writer->write(record);
            ++missing_host_record_ctrl_num_count;
            continue;
        }

        std::string host_id(subfields.getFirstSubfieldWithCode('w'));
        if (StringUtil::StartsWith(host_id, "(DE-576)"))
            host_id = host_id.substr(8);
        const auto &parent_isbn_or_issn_iter(parent_id_to_isbn_and_issn_map.find(host_id));
        if (parent_isbn_or_issn_iter == parent_id_to_isbn_and_issn_map.end()) {
            marc_writer->write(record);
            ++missing_isbn_or_issn_count;
            continue;
        }

        if (MiscUtil::IsPossibleISSN(parent_isbn_or_issn_iter->second)) {
            subfields.addSubfield('x', parent_isbn_or_issn_iter->second);
            _773_field->setContents(subfields, _773_field->getIndicator1(), _773_field->getIndicator2());
            ++issns_added;
        } else { // Deal with ISBNs.
            auto _020_field(record.findTag("020"));
            if (_020_field == record.end()) {
                record.insertField("020", { { 'a', parent_isbn_or_issn_iter->second } });
                ++isbns_added;
            } else if (_020_field->getFirstSubfieldWithCode('a').empty()) {
                _020_field->appendSubfield('a', parent_isbn_or_issn_iter->second);
                ++isbns_added;
            }
        }
        marc_writer->write(record);
    }

    if (verbose) {
        std::cout << ::progname << ": Read " << count << " records.\n";
        std::cout << ::progname << ": Added ISBN's to " << isbns_added << " article record(s).\n";
        std::cout << ::progname << ": Added ISSN's to " << issns_added << " article record(s).\n";
        std::cout << ::progname << ": " << missing_host_record_ctrl_num_count
                 << " articles had missing host record control number(s).\n";
        std::cout << ::progname << ": For " << missing_isbn_or_issn_count << " articles no host ISBN nor ISSN was found.\n";
    }
}


} // unnamed namespace


int Main(int argc, char **argv) {
    if (argc < 3)
        Usage();

    const std::string marc_input_filename(argv[1]);
    const std::string marc_output_filename(argv[2]);
    if (unlikely(marc_input_filename == marc_output_filename))
        LOG_ERROR("Master input file name equals output file name!");

    auto marc_reader(MARC::Reader::Factory(marc_input_filename));
    auto marc_writer(MARC::Writer::Factory(marc_output_filename));

    std::unordered_map<std::string, std::string> parent_id_to_isbn_and_issn_map;
    PopulateParentIdToISBNAndISSNMap(marc_reader.get(), &parent_id_to_isbn_and_issn_map);
    marc_reader->rewind();

    AddMissingISBNsOrISSNsToArticleEntries(marc_reader.get(), marc_writer.get(),
                                           parent_id_to_isbn_and_issn_map);

    return EXIT_SUCCESS;
}
