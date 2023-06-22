/** \file   IssnLookup.cc
 *  \brief   The Utility for extracting issn information from https://portal.issn.org/
 *  \author  Steven Lolong (steven.lolong@uni-tuebingen.de)
 *
 *  \copyright 2023 Tübingen University Library.  All rights reserved.
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
#include <nlohmann/json.hpp>
#include "Downloader.h"
#include "IssnLookup.h"


namespace IssnLookup {


void ExtractingData(const std::string &issn, const nlohmann::json &issn_info_json, ISSNInfo * const issn_info) {
    const std::string issn_uri("resource/ISSN/" + issn), issn_title_uri("resource/ISSN/" + issn + "#KeyTitle");
    if (issn_info_json.at("@graph").is_structured()) {
        for (auto ar : issn_info_json.at("@graph")) {
            if (ar.is_structured()) {
                if (ar.at("@id") == issn_uri) {
                    issn_info->issn_ = issn;
                    for (auto &[key, val] : ar.items()) {
                        if (key == "mainTitle")
                            issn_info->main_title_ = val;
                        if (key == "format")
                            issn_info->format_ = val;
                        if (key == "identifier")
                            issn_info->identifier_ = val;
                        if (key == "type")
                            issn_info->type_ = val;
                        if (key == "isPartOf")
                            issn_info->is_part_of_ = val;
                        if (key == "publication")
                            issn_info->publication_ = val;

                        if (key == "url") {
                            if (val.is_structured())
                                for (auto val_item : val)
                                    issn_info->urls_.emplace_back(val_item);
                            else
                                issn_info->urls_.emplace_back(val);
                        }

                        if (key == "name") {
                            if (val.is_structured())
                                for (auto val_item : val)
                                    issn_info->names_.emplace_back(val_item);
                            else
                                issn_info->names_.emplace_back(val);
                        }
                    }
                }
                if (ar.at("@id") == issn_title_uri) {
                    for (auto &[key, val] : ar.items()) {
                        if (key == "value")
                            issn_info->title_ = val;
                    }
                }
            }
        }
    }
}

bool GetISSNInfo(const std::string &issn, ISSNInfo * const issn_info) {
    const std::string issn_url("https://portal.issn.org/resource/ISSN/" + issn + "?format=json");

    Downloader downloader(issn_url, Downloader::Params());

    if (downloader.anErrorOccurred()) {
        LOG_WARNING("Error while downloading data for ISSN " + issn + ": " + downloader.getLastErrorMessage());
        return false;
    }

    // Check for rate limiting and error status codes:
    const HttpHeader http_header(downloader.getMessageHeader());
    if (http_header.getStatusCode() != 200) {
        LOG_WARNING("IssnLookup returned HTTP status code " + std::to_string(http_header.getStatusCode()) + "! for ISSN: " + issn);
        return false;
    }

    const std::string content_type(http_header.getContentType());
    if (content_type.find("application/json") == std::string::npos) {
        // Unfortunately if the ISSN doesnt exist, the page will
        // return status code 200 OK, but HTML instead of JSON, so we need to
        // detect this case manually.
        LOG_WARNING("IssnLookup returned no JSON (maybe invalid ISSN) for ISSN: " + issn);
        return false;
    }

    std::string issn_info_json(downloader.getMessageBody());
    nlohmann::json issn_info_json_tree;

    try {
        issn_info_json_tree = nlohmann::json::parse(issn_info_json);
    } catch (nlohmann::json::parse_error &ex) {
        std::string err(ex.what());
        LOG_ERROR("Failed to parse JSON! " + err);
        return false;
    }

    ExtractingData(issn, issn_info_json_tree, issn_info);

    return true;
}

void ISSNInfo::PrettyPrint() {
    std::cout << "mainTitle: " << main_title_ << std::endl;
    std::cout << "title: " << title_ << std::endl;
    std::cout << "format: " << format_ << std::endl;
    std::cout << "identifier: " << identifier_ << std::endl;
    std::cout << "type: " << type_ << std::endl;
    std::cout << "ISSN: " << issn_ << std::endl;
    std::cout << "isPartOf: " << is_part_of_ << std::endl;
    std::cout << "publication: " << publication_ << std::endl;
    std::cout << "url: " << std::endl;
    for (auto &url : urls_)
        std::cout << url << std::endl;
    std::cout << "name: " << std::endl;
    for (auto &name : names_)
        std::cout << name << std::endl;
}

} // namespace IssnLookup