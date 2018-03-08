/** \file krimdok_flag_pda_records.cc
 *  \brief A tool for adding a PDA field to KrimDok records.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *  \author Johannes Riedl (johannes.riedl@uni-tuebingen.de)
 *
 *  \copyright 2016,2017,2018 Universitätsbibliothek Tübingen.  All rights reserved.
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
#include "MARC.h"
#include "StringUtil.h"
#include "TimeUtil.h"
#include "util.h"


void Usage() {
    std::cerr << "Usage: " << ::progname << " no_of_years marc_input_file marc_output_file\n";
    std::exit(EXIT_FAILURE);
}


bool IsMatchingRecord(const MARC::Record &record, const std::vector<std::pair<MARC::Record::const_iterator, MARC::Record::const_iterator>> &local_block_boundaries,
                      std::vector<std::string> &matching_subfield_a_values)
{
    for (const auto local_block_boundary : local_block_boundaries) {
        std::vector<MARC::Record::const_iterator> fields;
        if (record.findFieldsInLocalBlock("852", "??", local_block_boundary, &fields) == 0)
            return false;

        for (const auto &field : fields) {
            std::vector<std::string> subfield_a_values(field->getSubfields().extractSubfields('a'));
                for (const auto &subfield_a_value : subfield_a_values)
                    for (const auto &matching_subfield_a_value : matching_subfield_a_values)
                        if (subfield_a_value == matching_subfield_a_value)
                            return true;
        }
    }
    return false;
}


bool IsMPIRecord(const MARC::Record &record, const std::vector<std::pair<MARC::Record::const_iterator, MARC::Record::const_iterator>> &local_block_boundaries) {
    static std::vector<std::string> subfield_a_values{ "DE-Frei85" };
    return IsMatchingRecord(record, local_block_boundaries, subfield_a_values);
}


bool IsUBOrIFKRecord(const MARC::Record &record, const std::vector<std::pair<MARC::Record::const_iterator, MARC::Record::const_iterator>> &local_block_boundaries) {
    static std::vector<std::string> subfield_a_values{ "DE-21", "DE-21-110" };
    return IsMatchingRecord(record, local_block_boundaries, subfield_a_values);
}


bool IsARecognisableYear(const std::string &year_candidate) {
    if (year_candidate.length() != 4)
        return false;

    for (char ch : year_candidate) {
        if (not StringUtil::IsDigit(ch))
            return false;
    }

    return true;
}


// If we can find a recognisable year in 260$c we return it, o/w we return the empty string.
std::string GetPublicationYear(const MARC::Record &record) {
    for (const auto &_260_field : record.getTagRange("260")) {
        for (const auto &year_candidate : _260_field.getSubfields().extractSubfields('c'))
            if (IsARecognisableYear(year_candidate))
                return year_candidate;
    }
    return "";
}


void FindNonMPIInstitutions(const MARC::Record &record,
                            const std::vector<std::pair<MARC::Record::const_iterator, MARC::Record::const_iterator>> &local_block_boundaries,
                            std::vector<std::string> * const non_mpi_institutions)
{
    non_mpi_institutions->clear();

    for (const auto &local_block_boundary : local_block_boundaries) {
        std::vector<MARC::Record::const_iterator> fields;
        if (record.findFieldsInLocalBlock("852", "??", local_block_boundary, &fields) == 0)
            return;

        for (const auto &field : fields) {
            std::vector<std::string> subfield_a_values(field->getSubfields().extractSubfields('a'));
            for (const auto &subfield_a_value : subfield_a_values)
                if (subfield_a_value != "DE-Frei85")
                    non_mpi_institutions->emplace_back(subfield_a_value);
        }
    }
}


void AddPDAFieldToRecords(const std::string &cutoff_year, MARC::Reader * const marc_reader,
                          MARC::Writer * const marc_writer)
{
    unsigned pda_field_added_count(0);
    while (MARC::Record record = marc_reader->read()) {
        if (not record.isMonograph()) {
            marc_writer->write(record);
            continue;
        }

        std::vector<std::pair<MARC::Record::const_iterator, MARC::Record::const_iterator>> local_block_boundaries;
        record.findAllLocalDataBlocks(&local_block_boundaries);
        if (IsMPIRecord(record, local_block_boundaries) and not IsUBOrIFKRecord(record, local_block_boundaries)) {
            const std::string publication_year(GetPublicationYear(record));
            if (publication_year >= cutoff_year) {
                std::vector<std::string> non_mpi_institutions;
                FindNonMPIInstitutions(record, local_block_boundaries, &non_mpi_institutions);
                if (non_mpi_institutions.empty()) {
                    ++pda_field_added_count;
                    record.insertField("PDA", { { 'a', "yes" } });
                    marc_writer->write(record);
                    continue;
                }
            }
        }

        marc_writer->write(record);
    }

    std::cout << "Added a PDA field to " << pda_field_added_count << " record(s).\n";
}


std::string GetCutoffYear(const unsigned no_of_years) {
    const unsigned current_year(StringUtil::ToUnsigned(TimeUtil::GetCurrentYear(TimeUtil::LOCAL)));
    return std::to_string(current_year - no_of_years);
}


int main(int argc, char *argv[]) {
    ::progname = argv[0];

    try {
        if (argc != 4)
            Usage();

        const unsigned no_of_years(StringUtil::ToUnsigned(argv[1]));
        const std::unique_ptr<MARC::Reader> marc_reader(MARC::Reader::Factory(argv[2], MARC::Reader::AUTO));
        const std::unique_ptr<MARC::Writer> marc_writer(MARC::Writer::Factory(argv[3], MARC::Writer::AUTO));
        AddPDAFieldToRecords(GetCutoffYear(no_of_years), marc_reader.get(), marc_writer.get());
    } catch (const std::exception &x) {
        logger->error("caught exception: " + std::string(x.what()));
    }
}
