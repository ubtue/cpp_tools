/*  \brief Utility Functions for Lobid API (HBZ) to get title data, norm data (GND) and organisational data
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
#include "LobidUtil.h"
#include <unordered_map>
#include "Downloader.h"
#include "JSON.h"
#include "UrlUtil.h"
#include "util.h"


namespace LobidUtil {


std::unordered_map<std::string, const std::shared_ptr<const JSON::ObjectNode>> url_to_lookup_result_cache;


static std::string BASE_URL_GND = "http://lobid.org/gnd/search?format=json";
static std::string BASE_URL_ORGANISATIONS = "http://lobid.org/organisations/search?format=json";
static std::string BASE_URL_RESOURCES = "http://lobid.org/resources/search?format=json";


void AddUrlParams(std::string * const url, const std::string &key, const std::unordered_map<std::string, std::string> &params) {
    unsigned i(0);
    for (const auto &key_and_value : params) {
        if (i == 0)
            *url += "&" + key + "=";
        else
            *url += UrlUtil::UrlEncode(" AND ");
        *url += UrlUtil::UrlEncode(key_and_value.first + ":" + key_and_value.second);
        ++i;
    }
}


const std::string BuildUrl(const std::string &base_url, const std::unordered_map<std::string, std::string> &query_params,
                           const std::unordered_map<std::string, std::string> &filter_params,
                           const std::string &additional_query_params)
{
    std::string url(base_url);
    AddUrlParams(&url, "q", query_params);
    if (not additional_query_params.empty())
        url += UrlUtil::UrlEncode(" AND " + additional_query_params);
    AddUrlParams(&url, "filter", filter_params);
    return url;
}


const std::shared_ptr<const JSON::ObjectNode> Query(const std::string &url, const bool allow_multiple_results) {
    LOG_DEBUG(url);
    const auto url_and_lookup_result(url_to_lookup_result_cache.find(url));
    if (url_and_lookup_result != url_to_lookup_result_cache.end())
        return url_and_lookup_result->second;

    Downloader downloader(url);
    if (downloader.anErrorOccurred())
        LOG_ERROR(downloader.getLastErrorMessage());

    JSON::Parser json_parser(downloader.getMessageBody());
    std::shared_ptr<JSON::JSONNode> root_node;
    if (not (json_parser.parse(&root_node)))
        LOG_ERROR("failed to parse returned JSON: " + json_parser.getErrorMessage() + "(input was: "
                  + downloader.getMessageBody() + ")");

    const std::shared_ptr<const JSON::ObjectNode> root_object(JSON::JSONNode::CastToObjectNodeOrDie("root", root_node));
    url_to_lookup_result_cache.emplace(url, root_object);

    const unsigned total_items(root_object->getIntegerValue("totalItems"));
    if (total_items == 0) {
        LOG_WARNING("empty result for query: " + url);
        return nullptr;
    } else if (not allow_multiple_results and total_items > 1) {
        LOG_WARNING("multiple results for query: " + url);
        return nullptr;
    }

    return root_object;
}


const std::string QueryAndLookupString(const std::string &url, const std::string &path, const bool allow_multiple_results) {
    const auto root_object(Query(url, allow_multiple_results));
    if (root_object == nullptr)
        return "";

    return JSON::LookupString(path, root_object, "");
}


const std::vector<std::string> QueryAndLookupStrings(const std::string &url, const std::string &path, const bool allow_multiple_results) {
    const auto root_object(Query(url, allow_multiple_results));
    if (root_object == nullptr)
        return std::vector<std::string>{};

    return JSON::LookupStrings(path, root_object);
}


std::string GetAuthorGNDNumber(const std::string &author, const std::string &additional_query_params) {
    return QueryAndLookupString(BuildUrl(BASE_URL_GND, { { "preferredName", author } }, { { "type", "DifferentiatedPerson" } }, additional_query_params),
                                "/member/0/gndIdentifier", /* allow_multiple_results */ false);
}


std::vector<std::string> GetAuthorProfessions(const std::string &author, const std::string &additional_query_params) {
    return QueryAndLookupStrings(BuildUrl(BASE_URL_GND, { { "preferredName", author } }, { { "type", "DifferentiatedPerson" } }, additional_query_params),
                                 "/member/*/professionOrOccupation/*/label", /* allow_multiple_results */ false);
}


std::string GetOrganisationISIL(const std::string &organisation, const std::string &additional_query_params) {
    return QueryAndLookupString(BuildUrl(BASE_URL_ORGANISATIONS, { { "name", organisation } }, { },  additional_query_params),
                                "/member/0/isil", /* allow_multiple_results */ false);
}


std::string GetTitleDOI(const std::string &title, const std::string &additional_query_params) {
    return QueryAndLookupString(BuildUrl(BASE_URL_RESOURCES, { { "title", "\"" + title + "\"" } }, { }, additional_query_params),
                                "/member/0/doi/0", /* allow_multiple_results */ false);
}


} // namespace LobidUtil
