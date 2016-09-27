/** \file    extract_referenceterms.cc
 *  \brief   Generate a key-values list of  reference data (Hinweissätze)
 *  \author  Johannes Riedl
 */

/*
    Copyright (C) 2016, Library of the University of Tübingen

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

/*  We offer a list of tags and subfields where the primary data resides along
    with a list of tags and subfields where the synonym data is found and
    a list of unused fields in the title data where the synonyms can be stored 
*/

#include <iostream>
#include <map>
#include <vector>
#include <cstdlib>
#include "Compiler.h"
#include "FileUtil.h"
#include "MarcUtil.h"
#include "MediaTypeUtil.h"
#include "StringUtil.h"
#include "Subfields.h"
#include "util.h"


static unsigned record_count(0);
static unsigned read_in_count(0);


void Usage() {
    std::cerr << "Usage: " << ::progname << " reference_data_marc_input output\n";
    std::exit(EXIT_FAILURE);
}


std::string GetTag(const std::string &tag_and_subfields_spec) {
    return tag_and_subfields_spec.substr(0, 3);
}


std::string GetSubfieldCodes(const std::string &tag_and_subfields_spec) {
    return tag_and_subfields_spec.substr(3);
}


void ExtractSynonyms(File * const reference_data_marc_input, const std::set<std::string> &primary_tags_and_subfield_codes,
                     const std::set<std::string> &synonym_tags_and_subfield_codes,  std::vector<std::map<std::string, std::string>> * const synonym_maps) 
{
    while (const MarcUtil::Record record = MarcUtil::Record::BinaryFactory(reference_data_marc_input)) {
        std::set<std::string>::const_iterator primary;
        std::set<std::string>::const_iterator synonym;
        unsigned int i(0);
        for (primary = primary_tags_and_subfield_codes.begin(), synonym = synonym_tags_and_subfield_codes.begin();  
            primary != primary_tags_and_subfield_codes.end();
            ++primary, ++synonym, ++i) 
        {
            // Fill maps with synonyms
            std::vector<std::string> primary_values; 
            std::vector<std::string> synonym_values;              
          
            // Partly, a very specific term has a very specific one term circumscription (e.g. Wilhelminische Epoche => Deutschland)
            // Thus, we only insert terms we the synonym vector contains two elements to prevent inappropriate additions
            if (record.extractSubfields(GetTag(*primary), GetSubfieldCodes(*primary), &primary_values) and 
                record.extractSubfields(GetTag(*synonym), GetSubfieldCodes(*synonym), &synonym_values) and synonym_values.size() > 1) {
                    (*synonym_maps)[i].emplace(StringUtil::Join(primary_values, ','), StringUtil::Join(synonym_values, ','));
                    ++read_in_count;
                }
        }
    }
}


void WriteReferenceTermFile(File * const output, std::vector<std::map<std::string, std::string>> &synonym_maps){
    for (auto &sm : synonym_maps) {
        for (auto &entry : sm) {
             *output << entry.first << '|' << entry.second << '\n';
             ++record_count;
        }
    }
    std::cerr << "Extracted " << record_count << " record(s).\n";
}


int main(int argc, char **argv) {
    ::progname = argv[0];

    if (argc != 3)
        Usage();

    const std::string reference_data_marc_input_filename(argv[1]);
    std::unique_ptr<File> reference_data_marc_input(FileUtil::OpenInputFileOrDie(reference_data_marc_input_filename));

    const std::string output_filename(argv[2]);
    if (unlikely(reference_data_marc_input_filename == output_filename))
        Error("Reference data input file name equals output file name!");

    File output(output_filename, "w");
    if (not output)
        Error("can't open \"" + output_filename + "\" for writing!");

    try {
        // Determine possible mappings
        const std::string REFERENCE_DATA_PRIMARY_SPEC("150a");
        const std::string REFERENCE_DATA_SYNONYM_SPEC("260a");

        // Determine fields to handle
        std::set<std::string> primary_tags_and_subfield_codes;
        std::set<std::string> synonym_tags_and_subfield_codes;

        if (unlikely(StringUtil::Split(REFERENCE_DATA_PRIMARY_SPEC, ":", &primary_tags_and_subfield_codes) < 1))
            Error("Need at least one primary field");

        if (unlikely(StringUtil::Split(REFERENCE_DATA_SYNONYM_SPEC, ":", &synonym_tags_and_subfield_codes) < 1))
            Error("Need at least one synonym field");

        if (primary_tags_and_subfield_codes.size() != synonym_tags_and_subfield_codes.size())
            Error("Number of reference primary specs must match number of synonym specs");
             
        std::vector<std::map<std::string, std::string>> synonym_maps(synonym_tags_and_subfield_codes.size(), std::map<std::string, std::string>());
        
        // Extract the synonyms from reference marc data
        ExtractSynonyms(reference_data_marc_input.get(), primary_tags_and_subfield_codes, synonym_tags_and_subfield_codes, &synonym_maps);

        // Write a '|' separated list file
        WriteReferenceTermFile(&output, synonym_maps);

std::cerr << "Read in " << read_in_count << " record(s).\n";


    } catch (const std::exception &x) {
        Error("caught exception: " + std::string(x.what()));
    }
}
