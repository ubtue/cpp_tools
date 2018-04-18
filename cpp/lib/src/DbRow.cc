/** \file   DbRow.cc
 *  \brief  Implementation of the DbRow class.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2015,2018 Universitätsbibliothek Tübingen.  All rights reserved.
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
#include "DbRow.h"
#include <stdexcept>
#include "Compiler.h"
#include "util.h"


DbRow::DbRow(DbRow &&other) {
    row_ = other.row_;
    other.row_ = nullptr;
    field_sizes_ = other.field_sizes_;
    field_count_ = other.field_count_;
    other.field_count_ = 0;
    stmt_handle_ = other.stmt_handle_;
    other.stmt_handle_ = nullptr;
}


std::string DbRow::operator[](const size_t i) const {
    if (unlikely(i >= size()))
        throw std::out_of_range("index out of range in DbRow::operator[]: max. index is " + std::to_string(size() - 1)
                                + ", actual index was " + std::to_string(i) + "!");

    if (stmt_handle_ == nullptr)
        return std::string(row_[i], field_sizes_[i]);
    else {
        const char * const text(reinterpret_cast<const char *>(::sqlite3_column_text(stmt_handle_, i)));
        if (text == nullptr)
            LOG_ERROR("trying to access a NULL value as a string!");
        return text;
    }
}


std::string DbRow::operator[](const std::string &column_name) const {
    const auto name_and_index_iter(field_name_to_index_map_->find(column_name));
    if (unlikely(name_and_index_iter == field_name_to_index_map_->cend()))
        throw std::out_of_range("in DbRow::operator[](const std::string&): invalid column name \"" + column_name + "\"!");

    return operator[](name_and_index_iter->second);
}


bool DbRow::isNull(const size_t i) const {
    if (unlikely(i >= field_count_))
        throw std::out_of_range("in DbRow::isNull(const size_t i): index out of range in DbRow::isNull(const size_t i): max. "
                                "index is " + std::to_string(field_count_ - 1) + ", actual index was " + std::to_string(i) + "!");

    if (stmt_handle_ == nullptr)
        return row_[i] == nullptr;
    else
        return ::sqlite3_column_type(stmt_handle_, i) == SQLITE_NULL;
}


bool DbRow::isNull(const std::string &column_name) const {
    const auto name_and_index_iter(field_name_to_index_map_->find(column_name));
    if (unlikely(name_and_index_iter == field_name_to_index_map_->cend()))
        throw std::out_of_range("in DbRow::isNull(const std::string &column_name): invalid column name \""
                                 + column_name + "\"!");
    return isNull(name_and_index_iter->second);
}

