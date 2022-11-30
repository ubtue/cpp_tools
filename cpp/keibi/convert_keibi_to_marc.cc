/** \brief Convert the KeiBi Database entries to MARC 21 Records
 *  \author Johannes Riedl
 *
 *  \copyright 2021 Universitätsbibliothek Tübingen.  All rights reserved.
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

#include <functional>
#include <iostream>
#include <iomanip>
#include <map>
#include <sstream>
#include "DbConnection.h"
#include "FileUtil.h"
#include "IniFile.h"
#include "MARC.h"
#include "StringUtil.h"
#include "TimeUtil.h"
#include "UBTools.h"
#include "util.h"


namespace {

using ConversionFunctor = std::function<void(const std::string, const char, MARC::Record * const, const std::string)>;
const std::string KEIBI_QUERY("SELECT * FROM citations");
const char SEPARATOR_CHAR('|');
const std::string bibtexEntryType_field("bibtexEntryType");


struct DbFieldToMARCMapping {
    const std::string db_field_name_;
    const std::string marc_tag_;
    const char subfield_code_;
    std::function<void(MARC::Record * const, const std::string)> extraction_function_;
    DbFieldToMARCMapping(const std::string &db_field_name, const std::string marc_tag, const char subfield_code,
                         ConversionFunctor extraction_function) :
                         db_field_name_(db_field_name), marc_tag_(marc_tag),
                         subfield_code_(subfield_code),
                         extraction_function_(std::bind(extraction_function, marc_tag, subfield_code, std::placeholders::_1, std::placeholders::_2)) {}
};

const auto DbFieldToMarcMappingComparator = [](const DbFieldToMARCMapping &lhs, const DbFieldToMARCMapping &rhs) { return lhs.db_field_name_ < rhs.db_field_name_;};
using DbFieldToMARCMappingMultiset = std::multiset<DbFieldToMARCMapping, decltype(DbFieldToMarcMappingComparator)>;


enum BIBTEX_ENTRY_TYPES { INPROCEEDINGS, ARTICLE, BOOK, COLLECTION, UNKNOWN};
const std::map<std::string, int> STRING_TO_BITEX_ENTRY_TYPE {
   { "inproceedings", BIBTEX_ENTRY_TYPES::INPROCEEDINGS },
   { "article", BIBTEX_ENTRY_TYPES::ARTICLE },
   { "book", BIBTEX_ENTRY_TYPES::BOOK },
   { "collection", BIBTEX_ENTRY_TYPES::COLLECTION }
};


MARC::Record * CreateNewRecord(const std::string &keibi_uid, const std::string &bibtex_description) {
    std::ostringstream formatted_number;
    formatted_number << std::setfill('0') << std::setw(8) << std::atoi(keibi_uid.c_str());
    const std::string ppn("KEI" + formatted_number.str());

    MARC::Record::BibliographicLevel type_of_record;
    const auto type_candidate(STRING_TO_BITEX_ENTRY_TYPE.find(bibtex_description));
    if (type_candidate != STRING_TO_BITEX_ENTRY_TYPE.end()) {
       switch (type_candidate->second) {
           case BIBTEX_ENTRY_TYPES::BOOK:
               type_of_record = MARC::Record::BibliographicLevel::MONOGRAPH_OR_ITEM;
               return new MARC::Record(MARC::Record::TypeOfRecord::LANGUAGE_MATERIAL, type_of_record, ppn);
           case BIBTEX_ENTRY_TYPES::ARTICLE:
               type_of_record = MARC::Record::BibliographicLevel::MONOGRAPHIC_COMPONENT_PART;
               return new MARC::Record(MARC::Record::TypeOfRecord::LANGUAGE_MATERIAL, type_of_record, ppn);
           case BIBTEX_ENTRY_TYPES::COLLECTION:
               type_of_record = MARC::Record::BibliographicLevel::MONOGRAPHIC_COMPONENT_PART;
               return new MARC::Record(MARC::Record::TypeOfRecord::LANGUAGE_MATERIAL, type_of_record, ppn);
           case BIBTEX_ENTRY_TYPES::INPROCEEDINGS:
               type_of_record = MARC::Record::BibliographicLevel::MONOGRAPHIC_COMPONENT_PART;
               auto new_record(new MARC::Record(MARC::Record::TypeOfRecord::LANGUAGE_MATERIAL, type_of_record, ppn));
               new_record->insertField("655", 'a', "Konferenzschrift");
               return new_record;
       }
   }
   return new MARC::Record(MARC::Record::TypeOfRecord::LANGUAGE_MATERIAL, MARC::Record::BibliographicLevel::UNDEFINED, ppn);
}


[[noreturn]] void Usage() {
    ::Usage("db_inifile map_file marc_output");
}


void InsertField(const std::string &tag, const char subfield_code, MARC::Record * const record, const std::string &data) {
    if (data.length())
        record->insertField(tag, subfield_code, data);
}


void IsReview(const std::string &tag, const char subfield_code, MARC::Record * const record, const std::string &data) {
    if (data.length() and data != "0")
        record->insertField(tag, subfield_code, "Rezension");
}


void InsertCreationField(const std::string &tag, const char, MARC::Record * const record, const std::string &data) {
    if (data.length()) {
        static ThreadSafeRegexMatcher date_matcher("((\\d{4})-\\d{2}-\\d{2})[\\t\\s]+\\d{2}:\\d{2}:\\d{2}");
        if (const auto &match_result = date_matcher.match(data)) {
            if (match_result[1] == "0000-00-00")
                record->insertField(tag, "000101s2000    x |||||      00| ||ger c");
            else
                record->insertField(tag, StringUtil::Filter(match_result[1], "-").substr(2) + "s" + match_result[2] +"    xx |||||      00| ||ger c");
            return;
        } else
            LOG_ERROR("Invalid date format \"" + data + "\"");
    }
    // Fallback with dummy data
    record->insertField(tag, "000101s2000    xx |||||      00| ||ger c");

}


void InsertAuthors(const std::string, const char, MARC::Record * const record, const std::string &data) {
     if (data.length()) {
         std::vector<std::string> authors;
         std::string author, further_parts;
         std::string data_to_split(data);
         while (StringUtil::SplitOnString(data_to_split, " and ", &author, &further_parts)) {
             authors.emplace_back(author);
             data_to_split = further_parts;
         }
         authors.emplace_back(data_to_split);


         record->insertField("100", { { 'a', authors[0] }, { '4', "aut" }, {'e', "VerfasserIn" } });
         for (auto further_author = authors.begin() + 1; further_author != authors.end(); ++further_author)
              record->insertField("700", { { 'a',  *further_author }, { '4', "aut" }, { 'e', "VerfasserIn" } });
    }
}


void InsertOrForceSubfield(const std::string &tag, const char subfield_code, MARC::Record * const record, const std::string &data) {
    if (data.length()){
        if (not record->hasTag(tag)) {
            InsertField(tag, subfield_code, record, data);
            return;
        }
        for (auto &field : record->getTagRange(tag)) {
              // FIXME: Do not necessarily replace
             field.insertOrReplaceSubfield(subfield_code, data);
        }
    }
}


void InsertEditors(const std::string, const char, MARC::Record * const record, const std::string &data) {
    if (data.length()) {
         std::vector<std::string> editors;
         std::string editor, further_parts;
         std::string data_to_split(data);
         while (StringUtil::SplitOnString(data_to_split, " and ", &editor, &further_parts)) {
             editors.emplace_back(editor);
             data_to_split = further_parts;
         }
         for (const auto &further_editor : editors )
              record->insertField("700", { { 'a',  further_editor }, { '4', "edt" }, { 'e', "HerausgeberIn" }});
    }
}

void ConvertCitations(DbConnection * const db_connection,
                      const DbFieldToMARCMappingMultiset &dbfield_to_marc_mappings,
                      MARC::Writer * const marc_writer)
{
    db_connection->queryOrDie(KEIBI_QUERY);
    DbResultSet result_set(db_connection->getLastResultSet());
    while (const auto row = result_set.getNextRow()) {
        MARC::Record * const new_record(CreateNewRecord(row["uid"], row[bibtexEntryType_field]));
        for (auto dbfield_to_marc_mapping(dbfield_to_marc_mappings.begin());
             dbfield_to_marc_mapping != dbfield_to_marc_mappings.end();
             ++dbfield_to_marc_mapping)
        {
            dbfield_to_marc_mapping->extraction_function_(new_record, row[dbfield_to_marc_mapping->db_field_name_]);
        }
        // Dummy entries
        new_record->insertField("005", TimeUtil::GetCurrentDateAndTime("%Y%m%d%H%M%S") + ".0");
        marc_writer->write(*new_record);
        delete new_record;
    }
}


const std::map<std::string, ConversionFunctor> name_to_functor_map {
    {  "InsertField", InsertField },
    {  "IsReview", IsReview },
    {  "InsertCreationField", InsertCreationField },
    {  "InsertAuthors", InsertAuthors },
    {  "InsertOrForceSubfield", InsertOrForceSubfield },
    {  "InsertEditors", InsertEditors },
};

ConversionFunctor GetConversionFunctor(const std::string &functor_name) {
    if (not name_to_functor_map.contains(functor_name))
        LOG_ERROR("Unknown functor " + functor_name);
    return name_to_functor_map.find(functor_name)->second;
}


void ExtractTagAndSubfield(const std::string combined, std::string * tag, char * subfield_code) {
    bool is_no_subfield_tag(StringUtil::StartsWith(combined, "00"));
    if (combined.length() != 4 and not is_no_subfield_tag)
        LOG_ERROR("Invalid Tag and Subfield format " + combined);
    *tag = combined.substr(0,3);
    *subfield_code = is_no_subfield_tag ? ' ' :  combined[3];
}


void CreateDbFieldToMarcMappings(File * const map_file, DbFieldToMARCMappingMultiset * const dbfield_to_marc_mappings) {
    unsigned linenum(0);
    while (not map_file->eof()) {
        ++linenum;
        std::string line;
        map_file->getline(&line);
        StringUtil::Trim(&line);
        std::vector<std::string> mapping;
        StringUtil::SplitThenTrim(line, SEPARATOR_CHAR, " \t", &mapping);
        if (unlikely(mapping.size() < 2 and line.back() != SEPARATOR_CHAR)) {
            LOG_WARNING("Invalid line format in line " + std::to_string(linenum));
            continue;
        }
        static ThreadSafeRegexMatcher tag_subfield_and_functorname("(?i)([a-z0-9]{3,4})\\s+\\((\\p{L}+)\\)\\s*");
        const std::vector<std::string> extraction_rules(mapping.begin() + 1, mapping.end());
        for (const auto &extraction_rule : extraction_rules) {
             std::string tag;
             char subfield_code;
             ConversionFunctor conversion_functor;
             if (const auto match_result = tag_subfield_and_functorname.match(extraction_rule)) {
                 ExtractTagAndSubfield(match_result[1], &tag, &subfield_code);
                 conversion_functor = GetConversionFunctor(match_result[2]);
             } else if (extraction_rule.length() >= 3 && extraction_rule.length() <= 4){
                 ExtractTagAndSubfield(extraction_rule, &tag, &subfield_code);
                 conversion_functor = GetConversionFunctor("InsertField");
             } else
                 LOG_ERROR("Invalid extraction rule: " + extraction_rule);

             dbfield_to_marc_mappings->emplace(DbFieldToMARCMapping(mapping[0], tag, subfield_code, conversion_functor));
        }
    }
}

} // unnamed namespace


int Main(int argc, char *argv[]) {
    if (argc != 4)
        Usage();
    const std::string ini_file_path(argv[1]);
    const std::string map_file_path(argv[2]);
    const std::string marc_output_path(argv[3]);

    DbConnection db_connection(DbConnection::MySQLFactory(IniFile(ini_file_path)));
    std::unique_ptr<File> map_file(FileUtil::OpenInputFileOrDie(map_file_path));
    const std::unique_ptr<MARC::Writer> marc_writer(MARC::Writer::Factory(marc_output_path));
    DbFieldToMARCMappingMultiset dbfield_to_marc_mappings(DbFieldToMarcMappingComparator);
    CreateDbFieldToMarcMappings(map_file.get(), &dbfield_to_marc_mappings);
    ConvertCitations(&db_connection, dbfield_to_marc_mappings, marc_writer.get());

    return EXIT_SUCCESS;
}



