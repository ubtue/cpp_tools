/** \brief A tool to find changed article records for our partners in Cologne.
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

#include <unordered_set>
#include <cstdlib>
#include "DbConnection.h"
#include "Downloader.h"
#include "JSON.h"
#include "MARC.h"
#include "StringUtil.h"
#include "UBTools.h"
#include "util.h"


namespace {


[[noreturn]] void Usage() {
    ::Usage("marc_title_input marc_article_output\n"
            "Extracts changed article records that are contained in journals marked in the \"koe\" column in Zeder.");
}


const std::string IXTHEO_ZEDER_URL(
    "http://www-ub.ub.uni-tuebingen.de/zeder/cgi-bin/zeder.cgi?action=get&Dimension=wert&Bearbeiter=&Instanz=ixtheo");


void GetZederJSON(std::string * const json_blob) {
    Downloader downloader(IXTHEO_ZEDER_URL);
    if (downloader.anErrorOccurred())
        LOG_ERROR("failed to download Zeder data: " + downloader.getLastErrorMessage());

    const auto http_response_code(downloader.getResponseCode());
    if (http_response_code < 200 or http_response_code > 399)
        LOG_ERROR("got bad HTTP response code: " + std::to_string(http_response_code));

    *json_blob = downloader.getMessageBody();
}


std::string GetString(const std::shared_ptr<JSON::ObjectNode> &journal_node, const std::string &key) {
    if (not journal_node->hasNode(key))
        return "";

    const auto value(journal_node->getStringNode(key)->getValue());
    return value == "NV" ? "" : value;
}


void DetermineSuperiorPPNsOfInterest(std::unordered_set<std::string> * const superior_ppns_of_interest) {
    std::string json_blob;
    GetZederJSON(&json_blob);

    JSON::Parser parser(json_blob);
    std::shared_ptr<JSON::JSONNode> tree_root;
    if (not parser.parse(&tree_root))
        LOG_ERROR("failed to parse the Zeder JSON: " + parser.getErrorMessage());

    const auto root_node(JSON::JSONNode::CastToObjectNodeOrDie("tree_root", tree_root));
    if (not root_node->hasNode("daten"))
        LOG_ERROR("top level object of Zeder JSON does not have a \"daten\" key!");

    const auto daten(JSON::JSONNode::CastToArrayNodeOrDie("daten", root_node->getNode("daten")));

    unsigned total_journal_count(0), relevant_journal_count(0);
    for (const auto &entry : *daten) {
        ++total_journal_count;
        const auto journal_object(JSON::JSONNode::CastToObjectNodeOrDie("entry", entry));

        const auto koe(GetString(journal_object, "koe"));
        if (koe.empty())
            continue;

        const auto print_ppn(GetString(journal_object, "pppn"));
        const auto online_ppn(GetString(journal_object, "eppn"));

        bool found_at_least_one(false);
        if (not print_ppn.empty()) {
            superior_ppns_of_interest->emplace(print_ppn);
            found_at_least_one = true;
        }
        if (not online_ppn.empty()) {
            superior_ppns_of_interest->emplace(online_ppn);
            found_at_least_one = true;
        }
        if (found_at_least_one)
            ++relevant_journal_count;
    }

    LOG_INFO("Found " + std::to_string(relevant_journal_count) + " relevant journals out of a total of "
             + std::to_string(total_journal_count) + " in Zeder.");
}


void ExtractChangedRelevantArticles(MARC::Reader * const marc_reader, MARC::Writer * const marc_writer,
                                    const std::unordered_set<std::string> &superior_ppns_of_interest)
{
    DbConnection db_connection(UBTools::GetTuelibPath() + "cologne_article_hashes.sq3", DbConnection::CREATE);
    db_connection.queryOrDie("CREATE TABLE IF NOT EXISTS record_hashes ("
                             "    ppn TEXT PRIMARY KEY,"
                             "    hash TEXT NOT NULL"
                             ") WITHOUT ROWID");

    unsigned relevant_article_count(0), changed_article_count(0);
    while (auto record = marc_reader->read()) {
        if (not record.isArticle()
            or superior_ppns_of_interest.find(record.getSuperiorControlNumber()) == superior_ppns_of_interest.cend())
            continue;
        ++relevant_article_count;

        const auto current_hash(StringUtil::ToHexString(MARC::CalcChecksum(record)));

        db_connection.queryOrDie("SELECT hash FROM record_hashes WHERE ppn='" + record.getControlNumber() + "'");
        DbResultSet result_set(db_connection.getLastResultSet());
        std::string stored_hash;
        if (not result_set.empty()) {
            const DbRow row(result_set.getNextRow());
            stored_hash = row["hash"];
        }

        if (stored_hash != current_hash) {
            record.erase(MARC::Tag("LOK"));
            marc_writer->write(record);
            ++changed_article_count;
            db_connection.queryOrDie("REPLACE INTO record_hashes (ppn, hash) VALUES ('" + record.getControlNumber() + "', '"
                                     + current_hash + "')");
        }
    }

    LOG_INFO("Found " + std::to_string(relevant_article_count) + " of which " + std::to_string(changed_article_count)
             + " had not been encountered before or were changed.");
}


} // unnamed namespace


int Main(int argc, char *argv[]) {
    if (argc != 3)
        Usage();

    auto marc_reader(MARC::Reader::Factory(argv[1]));
    auto marc_writer(MARC::Writer::Factory(argv[2]));

    std::unordered_set<std::string> superior_ppns_of_interest;
    DetermineSuperiorPPNsOfInterest(&superior_ppns_of_interest);
    ExtractChangedRelevantArticles(marc_reader.get(), marc_writer.get(), superior_ppns_of_interest);

    return EXIT_SUCCESS;
}
