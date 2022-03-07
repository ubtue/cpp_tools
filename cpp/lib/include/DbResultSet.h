/** \file   DbResultSet.h
 *  \brief  Interface for the DbResultSet class.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2015-2021 Universitätsbibliothek Tübingen.  All rights reserved.
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


#include <algorithm>
#include <map>
#include <unordered_set>
#include <libpq-fe.h>
#include <mysql/mysql.h>
#include <sqlite3.h>
#include "DbRow.h"


class DbResultSet {
    friend class DbConnection;
    friend class MySQLDbConnection;
    friend class Sqlite3DbConnection;
    friend class PostgresDbConnection;
    DbResultSet *db_result_set_;

protected:
public:
    DbResultSet(DbResultSet &&other);

    /** \note If you need to instantiate a new DbResultSet instance while another is still live,
              you need to call this destructor explicitly on the live instance! (Yes, this is an evil hack!) */
    virtual ~DbResultSet();

    /** \return The number of rows in the result set. */
    inline virtual size_t size() const { return db_result_set_->size(); }

    /** \return The number of columns in a row. */
    inline virtual size_t getColumnCount() const { return db_result_set_->getColumnCount(); }

    inline bool empty() const { return size() == 0; }

    /** Typically you would call this in a loop like:
     *
     *  DbRow row;
     *  while (row = result_set.getNextRow())
     *      ProcessRow(row);
     *
     */
    inline virtual DbRow getNextRow() { return db_result_set_->getNextRow(); }

    inline virtual bool hasColumn(const std::string &column_name) const { return db_result_set_->hasColumn(column_name); }

    /** \return The set of all values in column "column" contained in this result set. */
    std::unordered_set<std::string> getColumnSet(const std::string &column);

    inline virtual const std::map<std::string, unsigned> getColumnNamesAndIndices() const {
        return db_result_set_->getColumnNamesAndIndices();
    }

protected:
    DbResultSet(): db_result_set_(nullptr) { }
    DbResultSet(DbResultSet * const db_result_set): db_result_set_(db_result_set) { }
};


class MySQLResultSet final : public DbResultSet {
    friend class DbConnection;
    friend class DbResultSet;
    friend class MySQLDbConnection;
    MYSQL_RES *mysql_res_;
    size_t no_of_rows_, column_count_;
    std::map<std::string, unsigned> field_name_to_index_map_;

private:
    MySQLResultSet(MYSQL_RES * const mysql_res);
    virtual ~MySQLResultSet();

    virtual size_t size() const { return no_of_rows_; }
    virtual size_t getColumnCount() const { return column_count_; }
    virtual DbRow getNextRow();
    virtual bool hasColumn(const std::string &column_name) const {
        return field_name_to_index_map_.find(column_name) != field_name_to_index_map_.cend();
    }
    virtual const std::map<std::string, unsigned> getColumnNamesAndIndices() const { return field_name_to_index_map_; }
};


class Sqlite3ResultSet final : public DbResultSet {
    friend class DbConnection;
    friend class DbResultSet;
    friend class Sqlite3DbConnection;
    sqlite3_stmt *stmt_handle_;
    size_t no_of_rows_, column_count_;
    std::map<std::string, unsigned> field_name_to_index_map_;

private:
    Sqlite3ResultSet(sqlite3_stmt * const stmt_handle);
    virtual ~Sqlite3ResultSet();

    virtual size_t size() const { return no_of_rows_; }
    virtual size_t getColumnCount() const { return column_count_; }
    virtual DbRow getNextRow();
    virtual bool hasColumn(const std::string &column_name) const {
        return field_name_to_index_map_.find(column_name) != field_name_to_index_map_.cend();
    }
    virtual const std::map<std::string, unsigned> getColumnNamesAndIndices() const { return field_name_to_index_map_; }
};


class PostgresResultSet final : public DbResultSet {
    friend class DbConnection;
    friend class DbResultSet;
    friend class PostgresDbConnection;
    PGresult *pg_result_;
    int pg_row_number_;
    size_t no_of_rows_, column_count_;
    std::map<std::string, unsigned> field_name_to_index_map_;

private:
    PostgresResultSet(PGresult * const pg_result);
    virtual ~PostgresResultSet() { }

    virtual size_t size() const { return no_of_rows_; }
    virtual size_t getColumnCount() const { return column_count_; }
    virtual DbRow getNextRow();
    virtual bool hasColumn(const std::string &column_name) const {
        return field_name_to_index_map_.find(column_name) != field_name_to_index_map_.cend();
    }
    virtual const std::map<std::string, unsigned> getColumnNamesAndIndices() const { return field_name_to_index_map_; }
};
