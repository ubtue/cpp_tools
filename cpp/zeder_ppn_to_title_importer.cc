/** \file   zeder_ppn_to_title_importer.cc
 *  \brief  Imports data from Zeder and writes a map file mapping online and print PPN's to journal titles.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *  \copyright 2018 Universitätsbibliothek Tübingen.  All rights reserved.
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
#include <unordered_map>
#include "Compiler.h"
#include "Downloader.h"
#include "FileUtil.h"
#include "JSON.h"
#include "MapIO.h"
#include "util.h"


namespace {


[[noreturn]] void Usage() {
    std::cerr << "Usage: " << ::progname << " [--min-log-level=min_verbosity] map_file_path\n";
    std::exit(EXIT_FAILURE);
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


void WriteMapEntry(File * const output, const std::string &key, const std::string &value) {
    if (not key.empty())
        MapIO::WriteEntry(output, key, value);
}


void ParseJSONandWriteMapFile(const std::string &map_file_path, const std::string &json_blob) {
    JSON::Parser parser(json_blob);
    std::shared_ptr<JSON::JSONNode> tree_root;
    if (not parser.parse(&tree_root))
        LOG_ERROR("failed to parse the Zeder JSON: " + parser.getErrorMessage());

    const auto map_file(FileUtil::OpenOutputFileOrDie(map_file_path));

    const auto root_node(JSON::JSONNode::CastToObjectNodeOrDie("tree_root", tree_root));
    if (not root_node->hasNode("daten"))
        LOG_ERROR("top level object of Zeder JSON does not have a \"daten\" key!");

    const auto daten(JSON::JSONNode::CastToArrayNodeOrDie("daten", root_node->getNode("daten")));

    unsigned journal_count(0), bad_count(0);
    for (const auto &entry : *daten) {
        ++journal_count;
        const auto journal_object(JSON::JSONNode::CastToObjectNodeOrDie("entry", entry));

        const auto row_id(journal_object->getIntegerNode("DT_RowId")->getValue());
        if (unlikely(not journal_object->hasNode("tit"))) {
            ++bad_count;
            LOG_WARNING("Zeder entry #" + std::to_string(row_id) + " is missing a title!");
            continue;
        }

        const auto title(journal_object->getStringNode("tit")->toString());
        const auto print_ppn(GetString(journal_object, "pppn"));
        const auto online_ppn(GetString(journal_object, "eppn"));

        if (print_ppn.empty() and online_ppn.empty()) {
            ++bad_count;
            LOG_WARNING("Zeder entry #" + std::to_string(row_id) + " is missing print and online PPN's!");
            continue;
        }

        WriteMapEntry(map_file.get(), print_ppn, title);
        WriteMapEntry(map_file.get(), online_ppn, title);
    }

    LOG_INFO("processed " + std::to_string(journal_count) + " journal entries of which " + std::to_string(bad_count) + " was/were bad.");
}


} // unnamed namespace


int Main(int argc, char *argv[]) {
    if (argc != 2)
        Usage();
    const std::string map_file_path(argv[1]);

    std::string json_blob;
    GetZederJSON(&json_blob);
    ParseJSONandWriteMapFile(map_file_path, json_blob);

    return EXIT_SUCCESS;
}
