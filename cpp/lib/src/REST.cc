/** \file    Elasticsearch.cc
 *  \brief   Implementation of utility functions for REST APIs.
 *  \author  Mario Trojan
 *
 *  \copyright 2018 Universitätsbiblothek Tübingen.  All rights reserved.
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
#include "REST.h"
#include <exception>


namespace REST {


std::string Query(const Url &url, const QueryType query_type, const std::string data, Downloader::Params params) {
    Downloader downloader(params);

    switch(query_type) {
    case QueryType::GET:
        downloader.newUrl(url);
        break;
    case QueryType::PUT:
        downloader.putData(url, data);
        break;
    }

    if (downloader.anErrorOccurred())
        throw std::runtime_error(downloader.getLastErrorMessage());

    return downloader.getMessageBody();
}


JSON::JSONNode *Query(const Url &url, const QueryType query_type, const std::shared_ptr<JSON::JSONNode> data, Downloader::Params params) {
    std::string json_in;
    if (data != nullptr)
        json_in = data->toString();
    std::string json_out(Query(url, query_type, json_in, params));
    JSON::Parser parser(json_out);
    JSON::JSONNode *tree_root;
    if (not parser.parse(&tree_root))
        throw std::runtime_error("could not parse JSON response");

    return tree_root;
}


} // namespace REST
