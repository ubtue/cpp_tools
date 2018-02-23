/** \file    REST.h
 *  \brief   Various utility functions for REST APIs.
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
#ifndef REST_H
#define REST_H


#include <string>
#include <memory>
#include "Downloader.h"
#include "JSON.h"
#include "Url.h"


namespace REST {


enum QueryType { GET, PUT };

std::string Query(const Url &url, const QueryType query_type, const std::string data="",
                  Downloader::Params params=Downloader::Params());

JSON::JSONNode *Query(const Url &url, const QueryType query_type,
                      const std::shared_ptr<JSON::JSONNode> data=nullptr,
                      Downloader::Params params=Downloader::Params());


} // namespace REST


#endif // ifndef REST_H
