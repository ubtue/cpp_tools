/** \file translation_db_tool.cc
 *  \brief A tool for reading/editing of the "translations" SQL table.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2016-2018 Universitätsbibliothek Tübingen.  All rights reserved.
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
#include <set>
#include <cstdlib>
#include <cstring>
#include "Compiler.h"
#include "DbConnection.h"
#include "DbResultSet.h"
#include "DbRow.h"
#include "IniFile.h"
#include "MiscUtil.h"
#include "SqlUtil.h"
#include "TranslationUtil.h"
#include "UBTools.h"
#include "util.h"


void Usage() {
    std::cerr << "Usage: " << ::progname << " command [args]\n\n";
    std::cerr << "       Possible commands are:\n";
    std::cerr << "       get_missing language_code\n";
    std::cerr << "       insert token language_code text translator\n";
    std::cerr << "       insert ppn gnd_code language_code text translator\n";
    std::cerr << "       update token language_code text translator\n";
    std::cerr << "       update ppn gnd_code language_code text translator\n";
    std::exit(EXIT_FAILURE);
}


// Replaces a comma with "\," and a slash with "\\".
std::string EscapeCommasAndBackslashes(const std::string &text) {
    std::string escaped_text;
    for (const auto ch : text) {
        if (unlikely(ch == ',' or ch == '\\'))
            escaped_text += '\\';
        escaped_text += ch;
    }

    return escaped_text;
}


unsigned GetMissing(DbConnection * const connection, const std::string &table_name,
                    const std::string &table_key_name, const std::string &category,
                    const std::string &language_code, const std::string &additional_condition = "")
{
    // Find a token/ppn where "language_code" is missing:
    connection->queryOrDie("SELECT distinct " + table_key_name + " FROM " + table_name + " WHERE " + table_key_name
                           + " NOT IN (SELECT distinct " + table_key_name + " FROM " + table_name
                           + " WHERE language_code = \"" + language_code + "\") "
                           + (additional_condition.empty() ? "" : " AND (" + additional_condition + ")")
                           + " ORDER BY RAND();");
    DbResultSet keys_result_set(connection->getLastResultSet());
    if (keys_result_set.empty())
        return 0;

    // Print the contents of all rows with the token from the last query on stdout:
    DbRow row(keys_result_set.getNextRow());
    const std::string matching_key(row[table_key_name]);
    connection->queryOrDie("SELECT * FROM " + table_name + " WHERE " + table_key_name + "='" + matching_key + "';");
    DbResultSet result_set(connection->getLastResultSet());
    if (result_set.empty())
        return 0;

    const std::set<std::string> column_names(SqlUtil::GetColumnNames(connection, table_name));
    const bool has_gnd_code(column_names.find("gnd_code") != column_names.cend());

    while ((row = result_set.getNextRow()))
        std::cout << EscapeCommasAndBackslashes(row[table_key_name]) << ',' << keys_result_set.size() << ','
                  << row["language_code"] << ',' << EscapeCommasAndBackslashes(row["translation"]) << ',' << category
                  << (has_gnd_code ? "," + row["gnd_code"] : "") << '\n';

    return result_set.size();
}


unsigned GetMissingVuFindTranslations(DbConnection * const connection, const std::string &language_code) {
    return GetMissing(connection, "vufind_translations", "token", "vufind_translations", language_code);
}


unsigned GetMissingKeywordTranslations(DbConnection * const connection, const std::string &language_code) {
    return GetMissing(connection, "keyword_translations", "ppn", "keyword_translations", language_code, "status != \"reliable_synonym\" AND status != \"unreliable_synonym\"");
}


unsigned GetExisting(DbConnection * const connection, const std::string &table_name,
                    const std::string &table_key_name, const std::string &category,
                    const std::string &language_code, const std::string &index_value)
{
    // Find a token/ppn where "language_code" is missing:
    connection->queryOrDie("SELECT distinct " + table_key_name + " FROM " + table_name + " WHERE " + table_key_name +
                 " NOT IN (SELECT distinct " + table_key_name + " FROM " + table_name +
                 " WHERE language_code = \"" + language_code + "\") ORDER BY RAND();");
    DbResultSet keys_result_set(connection->getLastResultSet());
    const size_t count(keys_result_set.size());

    connection->queryOrDie("SELECT * FROM " + table_name + " WHERE " + table_key_name + "='" + index_value + "';");
    DbResultSet result_set(connection->getLastResultSet());
    if (result_set.empty())
        return 0;

    const std::set<std::string> column_names(SqlUtil::GetColumnNames(connection, table_name));
    const bool has_gnd_code(column_names.find("gnd_code") != column_names.cend());

    while (const DbRow row = result_set.getNextRow())
        std::cout << EscapeCommasAndBackslashes(row[table_key_name]) << ',' << count << ',' << row["language_code"] << ','
                  << EscapeCommasAndBackslashes(row["translation"]) << ',' << category
                  << (has_gnd_code ? "," + row["gnd_code"] : "") << '\n';

    return result_set.size();
}


unsigned GetExistingVuFindTranslations(DbConnection * const connection, const std::string &language_code,
                                       const std::string &index_value)
{
    return GetExisting(connection, "vufind_translations", "token", "vufind_translations", language_code, index_value);
}


unsigned GetExistingKeywordTranslations(DbConnection * const connection, const std::string &language_code,
                                        const std::string &index_value)
{
    return GetExisting(connection, "keyword_translations", "ppn", "keyword_translations", language_code, index_value);
}



void InsertIntoVuFindTranslations(DbConnection * const connection, const std::string &token,
                                  const std::string &language_code, const std::string &text,
                                  const std::string &translator)
{
    connection->queryOrDie("INSERT INTO vufind_translations SET token=\"" + token + "\",language_code=\""
                           + language_code + "\",translation=\"" + connection->escapeString(text)
                           + "\",translator=\"" + translator + "\";");
}


void InsertIntoKeywordTranslations(DbConnection * const connection, const std::string &ppn,
                                   const std::string &gnd_code, const std::string &language_code,
                                   const std::string &text, const std::string &translator)
{
    connection->queryOrDie("INSERT INTO keyword_translations SET ppn=\"" + ppn + "\",gnd_code=\"" + gnd_code
                           + "\",language_code=\"" + language_code + "\",translation=\""
                           + connection->escapeString(text) + "\",origin=\"150\",status=\"new\"" + ",translator=\""
                           + translator + "\";");
}


void UpdateIntoVuFindTranslations(DbConnection * const connection, const std::string &token,
                                  const std::string &language_code, const std::string &text,
                                  const std::string &translator)
{
    connection->queryOrDie("UPDATE vufind_translations SET translation=\"" + connection->escapeString(text)
                           + "\", translator=\"" + translator + "\" WHERE token=\"" + token
                           + "\" AND language_code=\"" + language_code + "\";");
}


void UpdateIntoKeywordTranslations(DbConnection * const connection, const std::string &ppn,
                                   const std::string &gnd_code, const std::string &language_code,
                                   const std::string &text, const std::string &translator)
{
    connection->queryOrDie("UPDATE keyword_translations SET translation=\"" + connection->escapeString(text)
                           + "\", translator=\"" + translator + "\" WHERE ppn=\"" + ppn + "\" AND gnd_code=\""
                           + gnd_code + "\" AND language_code=\"" + language_code + "\""
                           + "AND status != \"unreliable\";");
}


void ValidateKeywordTranslation(DbConnection * const connection, const std::string &ppn,
                                const std::string &translation)
{
    const std::string query("SELECT translation FROM keyword_translations WHERE ppn = \"" + ppn + "\";");
    connection->queryOrDie(query);
    DbResultSet result_set(connection->getLastResultSet());

    while (const DbRow row = result_set.getNextRow()) {
        if (row["translation"].find("<") < row["translation"].find(">")
            and not(translation.find("<") < translation.find(">"))) {
            std::cout << "Your translation has to have a tag enclosed by '<' and '>'!";
            return;
        }
    }
}


const std::string CONF_FILE_PATH(UBTools::TUELIB_PATH + "translations.conf");


int main(int argc, char *argv[]) {
    ::progname = argv[0];

    try {
        if (argc < 2)
            Usage();

        const IniFile ini_file(CONF_FILE_PATH);
        const std::string sql_database(ini_file.getString("Database", "sql_database"));
        const std::string sql_username(ini_file.getString("Database", "sql_username"));
        const std::string sql_password(ini_file.getString("Database", "sql_password"));
        DbConnection db_connection(sql_database, sql_username, sql_password);

        if (std::strcmp(argv[1], "get_missing") == 0) {
            if (argc != 3)
                logger->error("\"get_missing\" requires exactly one argument: language_code!");
            const std::string language_code(argv[2]);
            if (not TranslationUtil::IsValidFake3Or4LetterEnglishLanguagesCode(language_code))
                logger->error("\"" + language_code + "\" is not a valid fake 3- or 4-letter english language code!");
            if (not GetMissingVuFindTranslations(&db_connection, language_code))
                GetMissingKeywordTranslations(&db_connection, language_code);
        } else if (std::strcmp(argv[1], "get_existing") == 0) {
            if (argc != 5)
                logger->error("\"get_existing\" requires exactly three arguments: language_code category index!");
            const std::string language_code(argv[2]);
            if (not TranslationUtil::IsValidFake3Or4LetterEnglishLanguagesCode(language_code))
                logger->error("\"" + language_code + "\" is not a valid fake 3- or 4-letter english language code!");
            const std::string category(argv[3]);
            const std::string index_value(argv[4]);
            if (category == "vufind_translations")
                GetExistingVuFindTranslations(&db_connection, language_code, index_value);
            else
                GetExistingKeywordTranslations(&db_connection, language_code, index_value);
        } else if (std::strcmp(argv[1], "insert") == 0) {
            if (argc != 6 and argc != 7)
                logger->error("\"insert\" requires four or five arguments: token or ppn, gnd_code (if ppn), "
                              "language_code, text, and translator!");

            const std::string language_code(argv[(argc == 6) ? 3 : 4]);
            if (not TranslationUtil::IsValidFake3Or4LetterEnglishLanguagesCode(language_code))
                logger->error("\"" + language_code + "\" is not a valid fake 3- or 4-letter english language code!");

            if (argc == 6)
                InsertIntoVuFindTranslations(&db_connection, argv[2], language_code, argv[4], argv[5]);
            else
                InsertIntoKeywordTranslations(&db_connection, argv[2], argv[3], language_code, argv[5], argv[6]);
        } else if (std::strcmp(argv[1], "update") == 0) {
            if (argc != 6 and argc != 7)
                logger->error("\"update\" requires four or five arguments: token or ppn, gnd_code (if ppn), "
                      "language_code, text and translator!");

            const std::string language_code(argv[(argc == 6) ? 3 : 4]);
            if (not TranslationUtil::IsValidFake3Or4LetterEnglishLanguagesCode(language_code))
                logger->error("\"" + language_code + "\" is not a valid fake 3-letter english language code!");

            if (argc == 6)
                UpdateIntoVuFindTranslations(&db_connection, argv[2], language_code, argv[4], argv[5]);
            else
                UpdateIntoKeywordTranslations(&db_connection, argv[2], argv[3], language_code, argv[5], argv[6]);
        } else if (std::strcmp(argv[1], "validate_keyword") == 0) {
            if (argc != 4)
                logger->error("\"get_missing\" requires exactly two argument: ppn translation!");
            const std::string ppn(argv[2]);
            const std::string translation(argv[3]);
            ValidateKeywordTranslation(&db_connection, ppn, translation);
        } else
            logger->error("unknown command \"" + std::string(argv[1]) + "\"!");
    } catch (const std::exception &x) {
        logger->error("caught exception: " + std::string(x.what()) + " (login is " + MiscUtil::GetUserName() + ")");
    }
}
