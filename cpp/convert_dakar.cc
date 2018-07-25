/** \file    convert_dakar.cc
 *  \brief   Augment the DAKAR database with authority data references for authors, keywords and
             CIC (Codex Iuris Canonici) references
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
#include <regex>
#include <vector>
#include <cstdlib>
#include "Compiler.h"
#include "DbConnection.h"
#include "DbResultSet.h"
#include "DbRow.h"
#include "IniFile.h"
#include "MARC.h"
#include "RegexMatcher.h"
#include "StringUtil.h"
#include "util.h"


const std::string CONF_FILE_PATH("/usr/local/var/lib/tuelib/dakar.conf");
const std::string NOT_AVAILABLE("N/A");

namespace {

[[noreturn]] void Usage() {
    std::cerr << "Usage: " << ::progname << " [--generate-list|--augment-db] authority_data" << '\n';
    std::cerr << "       no operation mode means --augment-db\n";
    std::exit(EXIT_FAILURE);
}


DbResultSet ExecSqlAndReturnResultsOrDie(const std::string &select_statement, DbConnection * const db_connection) {
    db_connection->queryOrDie(select_statement);
    return db_connection->getLastResultSet();
}


void GetAuthorsFromDB(DbConnection &db_connection, std::set<std::string> * const authors) {
    std::string distinct_author_query("SELECT DISTINCT autor FROM ikr");
    DbResultSet result_set(ExecSqlAndReturnResultsOrDie(distinct_author_query, &db_connection));
    while (const DbRow db_row = result_set.getNextRow()) {
        const std::string author_row(db_row["autor"]);
        std::vector<std::string> authors_in_row;
        StringUtil::Split(author_row, ';', &authors_in_row);
        for (auto &author : authors_in_row) {
            // Remove superfluous additions
            static std::regex to_strip("\\(Hrsg[\\.]\\)");
            author = std::regex_replace(author, to_strip , "");
            authors->emplace(StringUtil::TrimWhite(author));
        }
    }
}


void GetKeywordsFromDB(DbConnection &db_connection, std::set<std::string> * const keywords) {
    std::string distinct_keyword_query("SELECT DISTINCT stichwort FROM ikr");
    DbResultSet result_set(ExecSqlAndReturnResultsOrDie(distinct_keyword_query, &db_connection));
    while (const DbRow db_row = result_set.getNextRow()) {
        const std::string keyword_row(db_row["stichwort"]);
        std::vector<std::string> keywords_in_row;
        StringUtil::Split(keyword_row, ';', &keywords_in_row);
        for (const auto &keyword : keywords_in_row) {
            keywords->emplace(StringUtil::TrimWhite(keyword));
        }
    }
}


void GetCICFromDB(DbConnection &db_connection, std::set<std::string> * const cic_numbers) {
    std::string distinct_cic_query("SELECT DISTINCT cicbezug FROM ikr");
    DbResultSet result_set(ExecSqlAndReturnResultsOrDie(distinct_cic_query, &db_connection));
    while (const DbRow db_row = result_set.getNextRow()) {
        const std::string cic_row(db_row["cicbezug"]);
        std::vector<std::string> cics_in_row;
        StringUtil::Split(cic_row, ';', &cics_in_row);
        for (const auto &cic : cics_in_row) {
            cic_numbers->emplace(StringUtil::TrimWhite(cic));
        }
    }
}


void AssemblePrimaryAndSynonymKeywordEntry(const MARC::Record &record,
                                   const std::string gnd_number,
                                   std::unordered_multimap<std::string,std::string> * const keyword_to_gnd_map,
                                   const std::string primary_tag,
                                   const std::string subfield_spec,
                                   const std::string synonym_tag)
{
    const std::string primary(StringUtil::Join(record.getSubfieldAndNumericSubfieldValues(primary_tag, subfield_spec), " "));
    if (not primary.empty()) {
        keyword_to_gnd_map->emplace(primary, gnd_number);
        // Also get "Verweisungsformen"
        for (const auto &field : record.getTagRange(synonym_tag)) {
             const MARC::Subfields subfields(field.getContents());
             const std::string synonym(StringUtil::Join(subfields.extractSubfieldsAndNumericSubfields(subfield_spec), " "));
             if (not synonym.empty()) {
                 keyword_to_gnd_map->emplace(synonym, gnd_number);
             }
        }
    }

}


void ExtractAuthorityData(const std::string &authority_file,
                          std::unordered_multimap<std::string,std::string> * const author_to_gnd_map,
                          std::unordered_multimap<std::string,std::string> * const keyword_to_gnd_map,
                          std::unordered_map<std::string,std::string> * const cic_to_gnd_map)
{
    auto marc_reader(MARC::Reader::Factory(authority_file));
    auto authority_reader(marc_reader.get());
    while (const auto &record = authority_reader->read()) {
        std::string gnd_number;

        if (not MARC::GetGNDCode(record, &gnd_number))
            continue;

        // Authors
        const std::string author(StringUtil::Join(record.getSubfieldAndNumericSubfieldValues("100", "abcpnt9v"), " "));
        if (not author.empty()) {
            author_to_gnd_map->emplace(author, gnd_number);
            // Also add "Verweisungsform"
            for (const auto &field : record.getTagRange("400")) {
                const MARC::Subfields subfields(field.getContents());
                const std::string synonym(StringUtil::Join(subfields.extractSubfieldsAndNumericSubfields("abcpnt9v"), " "));
                if (not synonym.empty()) {
                    author_to_gnd_map->emplace(synonym, gnd_number);
                }
            }
            continue; // next entry
        }

        // CIC
        // Possible contents: number; number-number; number,number; number,number,number
        const std::string cic_110_field(StringUtil::Join(record.getSubfieldValues("110", "atf"), ","));
        if (cic_110_field == "Katholische Kirche,Codex iuris canonici,1983") {
            const std::string cic_code(StringUtil::Join(record.getSubfieldValues("110", 'p'), " "));
            if (not cic_code.empty()) {
                // Dakar uses '.' instead of ',' as a separator
                cic_to_gnd_map->emplace(StringUtil::Map(cic_code, ',', '.'), gnd_number);
                // We will not find reasonable keywords in this iteration
                continue;
            }
        }

        // Keywords
        AssemblePrimaryAndSynonymKeywordEntry(record, gnd_number, keyword_to_gnd_map, "110", "abcdnptx9v9g", "410");
        AssemblePrimaryAndSynonymKeywordEntry(record, gnd_number, keyword_to_gnd_map, "111", "abcdnptx9v9g", "411");
        AssemblePrimaryAndSynonymKeywordEntry(record, gnd_number, keyword_to_gnd_map, "130", "abcdnptx9v9g", "430");
        AssemblePrimaryAndSynonymKeywordEntry(record, gnd_number, keyword_to_gnd_map, "150", "abcdnptx9v9g", "450");
        AssemblePrimaryAndSynonymKeywordEntry(record, gnd_number, keyword_to_gnd_map, "151", "abcdnptx9v9g", "451");
    }
}


auto GenerateGNDLink = [](const std::string gnd) { return "XXX" + gnd + "XXX"; };

void MakeGNDLink(std::vector<std::string> * const gnds) {
    std::vector<std::string> formatted_values;
    std::transform(gnds->begin(), gnds->end(), std::back_inserter(formatted_values), GenerateGNDLink);
    gnds->swap(formatted_values);
}


// Wrapper for a single string to guarantee that the generation function is not implemented at two different places in the code
void MakeGNDLink(std::string * const gnd) {
     std::vector<std::string> temp({ *gnd });
     MakeGNDLink(&temp);
     *gnd = temp[0];
}


void GetAuthorGNDResultMap(DbConnection &db_connection,
                           const std::unordered_multimap<std::string, std::string> &all_authors_to_gnd_map,
                           std::unordered_map<std::string,std::string> * const author_to_gnds_result_map, const bool skip_empty=true, const bool generate_gnd_link=false)
{
     std::set<std::string> authors;
     GetAuthorsFromDB(db_connection, &authors);
     for (auto &author: authors) {
          auto author_and_gnds(all_authors_to_gnd_map.equal_range(author));
          std::vector<std::string> gnds;
          for (auto gnd(author_and_gnds.first); gnd != author_and_gnds.second; ++gnd)
              gnds.emplace_back(StringUtil::TrimWhite(gnd->second));
          if (not gnds.empty() or not skip_empty) {
              if (generate_gnd_link)
                  MakeGNDLink(&gnds);
              author_to_gnds_result_map->emplace(author, StringUtil::Join(gnds, ","));
          }
     }
}


void GetKeywordGNDResultMap(DbConnection &db_connection,
                     const std::unordered_multimap<std::string, std::string> &all_keywords_to_gnd_map,
                     std::unordered_map<std::string,std::string> * keyword_to_gnds_result_map, const bool skip_empty=true, const bool generate_gnd_link=false)
{
    std::set<std::string> keywords;
    GetKeywordsFromDB(db_connection, &keywords);
    for (auto &keyword : keywords) {
        const auto keyword_and_gnds(all_keywords_to_gnd_map.equal_range(keyword));
        std::vector<std::string> gnds;
        for (auto gnd(keyword_and_gnds.first); gnd != keyword_and_gnds.second; ++gnd)
            gnds.emplace_back(StringUtil::TrimWhite(gnd->second));
        if (not gnds.empty() or not skip_empty) {
            if (generate_gnd_link)
                MakeGNDLink(&gnds);
            keyword_to_gnds_result_map->emplace(keyword, StringUtil::Join(gnds, ","));
        }
    }
}


void GetCICGNDResultMap(DbConnection &db_connection,
                        const std::unordered_map<std::string, std::string> &all_cics_to_gnd_map,
                        std::unordered_map<std::string,std::string> * cic_to_gnd_result_map, const bool skip_empty=true, const bool generate_gnd_link=false)
{
    std::set<std::string> cics;
    GetCICFromDB(db_connection, &cics);
    for (const auto &cic : cics) {
        const auto cic_and_gnd(all_cics_to_gnd_map.find(cic));
        if (cic_and_gnd != all_cics_to_gnd_map.cend()) {
            std::string cic_gnd(StringUtil::TrimWhite((*cic_and_gnd).second));
            if (generate_gnd_link)
                MakeGNDLink(&cic_gnd);
            cic_to_gnd_result_map->emplace(cic, cic_gnd);
        }
        else if (not skip_empty)
           cic_to_gnd_result_map->emplace(cic, "");
    }
}


void AugmentDBEntries(DbConnection &db_connection,
                      const std::unordered_map<std::string,std::string> &author_to_gnds_result_map,
                      const std::unordered_map<std::string,std::string> &keyword_to_gnds_result_map,
                      const std::unordered_map<std::string,std::string> &cic_to_gnd_result_map) {
    // Iterate over Database
    const std::string ikr_query("SELECT id,autor,stichwort,cicbezug FROM ikr");
    DbResultSet result_set(ExecSqlAndReturnResultsOrDie(ikr_query, &db_connection));
    while (const DbRow db_row = result_set.getNextRow()) {
        // Authors
        const std::string author_row(db_row["autor"]);
        std::vector<std::string> authors_in_row;
        std::vector<std::string> author_gnd_numbers;
        bool author_gnd_seen(false);
        StringUtil::Split(author_row, ';', &authors_in_row);
        for (const auto &one_author : authors_in_row) {
             const auto author_gnds(author_to_gnds_result_map.find(StringUtil::TrimWhite(one_author)));
             if (author_gnds != author_to_gnds_result_map.cend()) {
                 author_gnd_numbers.emplace_back(author_gnds->second);
                 author_gnd_seen = true;
             } else
                 author_gnd_numbers.emplace_back(NOT_AVAILABLE);
        }
        // Only write back non-empty string if we have at least one reasonable entry
        const std::string a_gnd_content(author_gnd_seen ? StringUtil::Join(author_gnd_numbers, ";") : "");

        // Keywords
        const std::string keyword_row(db_row["stichwort"]);
        std::vector<std::string> keywords_in_row;
        std::vector<std::string> keyword_gnd_numbers;
        bool keyword_gnd_seen(false);
        StringUtil::Split(keyword_row, ';', &keywords_in_row);
        for (const auto one_keyword : keywords_in_row) {
            const auto keyword_gnds(keyword_to_gnds_result_map.find(StringUtil::TrimWhite(one_keyword)));
            if (keyword_gnds != keyword_to_gnds_result_map.cend()) {
                keyword_gnd_numbers.emplace_back(keyword_gnds->second);
                keyword_gnd_seen = true;
            } else {
                keyword_gnd_numbers.emplace_back(NOT_AVAILABLE);
            }
        }
        // Only write back non-empty string if we have at least one reasonable entry
        const std::string s_gnd_content(keyword_gnd_seen ? StringUtil::Join(keyword_gnd_numbers, ";") : "");

        //CIC
        const std::string cic_row(db_row["cicbezug"]);
        std::vector<std::string> cics_in_row;
        std::vector<std::string> cic_gnd_numbers;
        bool cic_gnd_seen(false);
        StringUtil::Split(cic_row, ';', &cics_in_row);
        for (const auto one_cic : cics_in_row) {
            const auto cic_gnd(cic_to_gnd_result_map.find(StringUtil::TrimWhite(one_cic)));
            if (cic_gnd != cic_to_gnd_result_map.cend()) {
               cic_gnd_numbers.emplace_back(cic_gnd->second);
               cic_gnd_seen = true;
            } else
               cic_gnd_numbers.emplace_back(NOT_AVAILABLE);
        }
        // Only write back non-empty string if we have at least one reasonable entry
        const std::string c_gnd_content(cic_gnd_seen ? StringUtil::Join(cic_gnd_numbers, ";") : "");

        // Write back the new entries
        const std::string id(db_row["id"]);
        const std::string update_row_query("UPDATE ikr SET a_gnd=\"" +  a_gnd_content + "\", s_gnd=\""
                                       + s_gnd_content + "\",c_gnd=\"" + c_gnd_content + "\""
                                       + " WHERE id=" + id);
        db_connection.queryOrDie(update_row_query);
    }
}


} //unnamed namespace


int Main(int argc, char **argv) {
     if (argc < 2)
         Usage();
     bool generate_list(false);
     bool skip_empty(true); //Do no insert entries without matches the final lookup lists
     bool generate_gnd_link(false); // Export GND numbers as links

     if (argc == 3 and (std::strcmp(argv[1], "--generate-list") != 0 and std::strcmp(argv[1], "--augment-db") != 0))
         Usage();

     if (std::strcmp(argv[1], "--generate-list") == 0) {
        generate_list=true;
        skip_empty=false;
        generate_gnd_link=true;
        ++argc, ++argv;
     }


     const std::string authority_file(argv[1]);


     const IniFile ini_file(CONF_FILE_PATH);
     const std::string sql_database(ini_file.getString("Database", "sql_database"));
     const std::string sql_username(ini_file.getString("Database", "sql_username"));
     const std::string sql_password(ini_file.getString("Database", "sql_password"));
     DbConnection db_connection(sql_database, sql_username, sql_password);


     std::unordered_multimap<std::string, std::string> all_authors_to_gnd_map;
     std::unordered_multimap<std::string, std::string> all_keywords_to_gnds_map;
     std::unordered_map<std::string, std::string> all_cics_to_gnd_map;
     ExtractAuthorityData(authority_file, &all_authors_to_gnd_map, &all_keywords_to_gnds_map, &all_cics_to_gnd_map);

     std::unordered_map<std::string,std::string> author_to_gnds_result_map;
     GetAuthorGNDResultMap(db_connection, all_authors_to_gnd_map, &author_to_gnds_result_map, skip_empty, generate_gnd_link);

     std::unordered_map<std::string,std::string> keyword_to_gnds_result_map;
     GetKeywordGNDResultMap(db_connection, all_keywords_to_gnds_map, &keyword_to_gnds_result_map, skip_empty, generate_gnd_link);

     std::unordered_map<std::string,std::string> cic_to_gnd_result_map;
     GetCICGNDResultMap(db_connection, all_cics_to_gnd_map, &cic_to_gnd_result_map, skip_empty, generate_gnd_link);
     if (generate_list) {
         std::ofstream author_out("/tmp/author_list.txt");
         for (const auto &author_and_gnds : author_to_gnds_result_map)
             author_out << author_and_gnds.first << "|" << author_and_gnds.second << '\n';
         std::ofstream keyword_out("/tmp/keyword_list.txt");
         for (const auto &keyword_and_gnds : keyword_to_gnds_result_map)
             keyword_out << keyword_and_gnds.first << "|" << keyword_and_gnds.second << '\n';
         std::ofstream cic_out("/tmp/cic_list.txt");
         for (const auto &cic_and_gnds : cic_to_gnd_result_map)
             cic_out << cic_and_gnds.first << "|" << cic_and_gnds.second << '\n';
     } else
         AugmentDBEntries(db_connection,author_to_gnds_result_map, keyword_to_gnds_result_map, cic_to_gnd_result_map);
     return EXIT_SUCCESS;
}

