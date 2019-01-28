/** \file    Elasticsearch.h
 *  \brief   Interface for the Elasticsearch class.
 *  \author  Dr. Johannes Ruscheinski
 *
 *  \copyright 2018,2019 Universitätsbibliothek Tübingen.  All rights reserved.
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
#pragma once


#include <map>
#include <string>
#include <unordered_set>
#include <vector>
#include "JSON.h"
#include "REST.h"


class Elasticsearch {
    std::string host_, index_, type_, username_, password_;
    bool ignore_ssl_certificates_;
public:
    enum RangeOperator { RO_GT, RO_GTE, RO_LT, RO_LTE, RO_NOOP };
public:
    /* \note   Some paramters are loaded from Elasticsearch.conf (located at the default ub_tools location) must contain
     *         a section name "Elasticsearch" w/ entries name "host", "username" (optional), "password" (optional) and
     *         "ignore_ssl_certificates" (optional, defaults to "false").
     */
    explicit Elasticsearch(const std::string &index, const std::string &type = "_doc");

    /** \return The number of documents in the index. */
    size_t size() const;

    void simpleInsert(const std::map<std::string, std::string> &fields_and_values);

    /** \brief Inserts or replaces logical document into the Elasticsearch index.
     *  \param document_id  An ID that must be unique per document, e.g. a MARC control number.
     *  \param document     A text blob that makes up the contents of a document.
     *  \note  If a document w/ "document_id" already exists, it will be replaced.
     */
    void insertOrUpdateDocument(const std::string &document_id, const std::string &document);

    bool deleteDocument(const std::string &document_id);

    /** \brief Returns all values, excluding duplicates contained in field "field". */
    std::unordered_set<std::string> selectAll(const std::string &field) const;

    /** \param  fields     If empty, all fields will be returned.
     *  \param  filter     If provided, oly results will be returned where each key in "filter" matches the corresponding value.
     *  \param  max_count  The maximum nuber of results to return.  -1 means to return all results.
     *  \return A map for each matched record.
     *  \note   Not all requested fields may be contained in each map!
     */
    std::vector<std::map<std::string, std::string>> simpleSelect(const std::set<std::string> &fields,
                                                                 const std::map<std::string, std::string> &filter = {},
                                                                 const int max_count = -1) const;

    inline std::vector<std::map<std::string, std::string>> simpleSelect(const std::set<std::string> &fields, const std::string &filter_field,
                                                                        const std::string &filter_value, const int max_count = -1) const
    { return simpleSelect(fields, std::map<std::string, std::string>{ { filter_field, filter_value } }, max_count); }

    /** \note Specify one or two range conditions. */
    bool deleteRange(const std::string &field, const RangeOperator operator1, const std::string &operand1,
                     const RangeOperator operator2 = RO_NOOP, const std::string &operand2 = "");
private:
    /** \brief A powerful general query.
     */
    std::shared_ptr<JSON::ObjectNode> query(const std::string &action, const REST::QueryType query_type, const JSON::ObjectNode &data) const;
};
