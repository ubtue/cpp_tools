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
#pragma once


#include <string>
#include <mysql/mysql.h>
#include <sqlite3.h>
#include "DbResultSet.h"
#include "util.h"


// Forward declaration:
class IniFile;


class DbConnection {
public:
    enum Type { T_MYSQL, T_SQLITE };
    enum TimeZone { TZ_SYSTEM, TZ_UTC };
    static const std::string DEFAULT_CONFIG_FILE_PATH;
private:
    Type type_;
    sqlite3 *sqlite3_;
    sqlite3_stmt *stmt_handle_;
    mutable MYSQL mysql_;
    bool initialised_;
public:
    enum OpenMode { READONLY, READWRITE, CREATE };
    enum Charset { UTF8MB3, UTF8MB4 };
public:
    explicit DbConnection(const TimeZone time_zone = TZ_SYSTEM); // Uses the ub_tools database.

    DbConnection(const std::string &database_name, const std::string &user, const std::string &passwd = "",
                 const std::string &host = "localhost", const unsigned port = MYSQL_PORT, const Charset charset = UTF8MB4,
                 const TimeZone time_zone = TZ_SYSTEM)
        { type_ = T_MYSQL; init(database_name, user, passwd, host, port, charset, time_zone); }

    // Expects to find entries named "sql_database", "sql_username" and "sql_password".  Optionally there may also
    // be an entry named "sql_host".  If this entry is missing a default value of "localhost" will be assumed.
    // Another optional entry is "sql_port".  If that entry is missing the default value MYSQL_PORT will be used.
    explicit DbConnection(const IniFile &ini_file, const std::string &ini_file_section = "Database", const TimeZone time_zone = TZ_SYSTEM);

    DbConnection(const std::string &database_path, const OpenMode open_mode);

    /** \brief Attemps to parse something like "mysql://ruschein:xfgYu8z@localhost:3345/vufind" */
    explicit DbConnection(const std::string &mysql_url, const Charset charset = UTF8MB4, const TimeZone time_zone = TZ_SYSTEM);

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

    /** \brief Reads SQL statements from "filename" and executes them.
     *  \note  Aborts if "filename" can't be read.
     *  \note  If the environment variable "UTIL_LOG_DEBUG" has been set "true", query statements will be
     *         logged to /usr/local/var/log/tuefind/sql_debug.log.
     */
    bool queryFile(const std::string &filename);

    /** \brief Reads SQL statements from "filename" and executes them.
     *  \note  Aborts printing an error message to stderr if an error occurred.
     *  \note  If the environment variable "UTIL_LOG_DEBUG" has been set "true", query statements will be
     *         logged to /usr/local/var/log/tuefind/sql_debug.log.
     */
    void queryFileOrDie(const std::string &filename);

    void insertIntoTableOrDie(const std::string &table_name, const std::map<std::string, std::string> &column_names_to_values_map);

    DbResultSet getLastResultSet();
    inline std::string getLastErrorMessage() const
        { return (type_ == T_MYSQL) ? ::mysql_error(&mysql_) : ::sqlite3_errmsg(sqlite3_); }

    /** \return The the number of rows changed, deleted, or inserted by the last statement if it was an UPDATE,
     *          DELETE, or INSERT.
     *  \note   Must be called immediately after calling "query()".
     */
    inline unsigned getNoOfAffectedRows() const
        { return (type_ == T_MYSQL) ? ::mysql_affected_rows(&mysql_) : ::sqlite3_changes(sqlite3_); }

    /** \note Converts the binary contents of "unescaped_string" into a form that can used as a string.
     *  \note This probably breaks for Sqlite if the string contains binary characters.
     */
    std::string escapeString(const std::string &unescaped_string, const bool add_quotes = false);
    inline std::string escapeAndQuoteString(const std::string &unescaped_string) {
        return escapeString(unescaped_string, /* add_quotes = */true);
    }
private:
    /** \note This constructor is for operations which do not require any existing database.
     *        It should only be used in static functions.
     */
    DbConnection(const std::string &user, const std::string &passwd, const std::string &host, const unsigned port, const Charset charset)
        { type_ = T_MYSQL; init(user, passwd, host, port, charset, TZ_SYSTEM); }

    void setTimeZone(const TimeZone time_zone);
    void init(const std::string &database_name, const std::string &user, const std::string &passwd,
              const std::string &host, const unsigned port, const Charset charset, const TimeZone time_zone);

    void init(const std::string &user, const std::string &passwd, const std::string &host, const unsigned port, const Charset charset,
              const TimeZone time_zone);
public:
    static void MySQLCreateDatabase(const std::string &database_name, const std::string &admin_user, const std::string &admin_passwd,
                                    const std::string &host = "localhost", const unsigned port = MYSQL_PORT,
                                    const Charset charset = UTF8MB4);

    static void MySQLCreateUser(const std::string &new_user, const std::string &new_passwd, const std::string &admin_user,
                                const std::string &admin_passwd, const std::string &host = "localhost", const unsigned port = MYSQL_PORT,
                                const Charset charset = UTF8MB4);

    static bool MySQLDatabaseExists(const std::string &database_name, const std::string &user, const std::string &passwd,
                                    const std::string &host = "localhost", const unsigned port = MYSQL_PORT,
                                    const Charset charset = UTF8MB4);

    static void MySQLImportFile(const std::string &sql_file, const std::string &database_name, const std::string &user,
                                const std::string &passwd, const std::string &host = "localhost", const unsigned port = MYSQL_PORT,
                                const Charset charset = UTF8MB4);

    static std::vector<std::string> MySQLGetDatabaseList(const std::string &user, const std::string &passwd,
                                                         const std::string &host = "localhost", const unsigned port = MYSQL_PORT,
                                                         const Charset charset = UTF8MB4);

    static void MySQLGrantAllPrivileges(const std::string &database_name, const std::string &database_user, const std::string &admin_user,
                                        const std::string &admin_passwd, const std::string &host = "localhost",
                                        const unsigned port = MYSQL_PORT, const Charset charset = UTF8MB4);
};
