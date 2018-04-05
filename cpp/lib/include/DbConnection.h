/** \file   DbConnection.h
 *  \brief  Interface for the DbConnection class.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2015-2018 Universitätsbibliothek Tübingen.  All rights reserved.
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
#ifndef DB_CONNECTION_H
#define DB_CONNECTION_H


#include <string>
#include <mysql/mysql.h>
#include <sqlite3.h>
#include "DbResultSet.h"
#include "util.h"


class DbConnection {
public:
    enum Type { T_MYSQL, T_SQLITE };
private:
    Type type_;
    sqlite3 *db_handle_;
    sqlite3_stmt *stmt_handle_;
    mutable MYSQL mysql_;
    bool initialised_;
public:
    enum OpenMode { READONLY, READWRITE, CREATE };
public:
    DbConnection(const std::string &database_name, const std::string &user, const std::string &passwd = "",
                 const std::string &host = "localhost", const unsigned port = MYSQL_PORT)
        { type_ = T_MYSQL; init(database_name, user, passwd, host, port); }

    DbConnection(const std::string &database_path, const OpenMode open_mode);

    /** \brief Attemps to parse something like "mysql://ruschein:xfgYu8z@localhost:3345/vufind" */
    DbConnection(const std::string &mysql_url);

    virtual ~DbConnection();

    inline Type getType() const { return type_; }

    /** \note If the environment variable "UTIL_LOG_DEBUG" has been set "true", query statements will be
     *        logged to /usr/local/var/log/tuefind/sql_debug.log.
     */
    bool query(const std::string &query_statement);

    /** \brief Executes an SQL statement and aborts printing an error message to stderr if an error occurred.
     *  \note If the environment variable "UTIL_LOG_DEBUG" has been set "true", query statements will be
     *        logged to /usr/local/var/log/tuefind/sql_debug.log.
     */
    void queryOrDie(const std::string &query_statement);

    DbResultSet getLastResultSet();
    inline std::string getLastErrorMessage() const
        { return (type_ == T_MYSQL) ? ::mysql_error(&mysql_) : ::sqlite3_errmsg(db_handle_); }

    /** \return The the number of rows changed, deleted, or inserted by the last statement if it was an UPDATE,
     *          DELETE, or INSERT.
     *  \note   Must be called immediately after calling "query()".
     */
    inline unsigned getNoOfAffectedRows() const
        { return (type_ == T_MYSQL) ? ::mysql_affected_rows(&mysql_) : ::sqlite3_changes(db_handle_); }

    /** Converts the binary contents of "unescaped_string" into a form that can used as a string (you still
        need to add quotes around it) in SQL statements. */
    std::string escapeString(const std::string &unescaped_string);
private:
    void init(const std::string &database_name, const std::string &user, const std::string &passwd,
              const std::string &host, const unsigned port);
};


#endif // ifndef DB_CONNECTION_H
