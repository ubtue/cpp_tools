/** \file   util.h
 *  \brief  Various utility functions that did not seem to logically fit anywhere else.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2014,2017,2018 Universitätsbibliothek Tübingen.  All rights reserved.
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
#ifndef UTIL_H
#define UTIL_H


#include <mutex>
#include <string>
#include <vector>
#include <cerrno>
#include <cstdio>
#include <cstring>
#include <unistd.h>
#include "Compiler.h"


// Macros to create strings describing where and why an error occurred. Must be macros to access __FILE__ and __LINE__.
// This gobble-dee-goop is necessary to turn __LINE__ into a string. See doctor dobs: http://www.ddj.com/dept/cpp/184403864
//
#define Stringize(S) ReallyStringize(S)
#define ReallyStringize(S) #S


/** A thread-safe logger class.
 * \note Set the environment variable LOGGER_FORMAT to control the output format of our logger.  So far we support
 *       "process_pids", "strip_call_site" and "no_decorations".  You may combine any of these, e.g. by separating them with
 *       commas.
 */
class Logger {
    friend Logger *LoggerInstantiator();
    std::mutex mutex_;
    int fd_;
    bool log_process_pids_, log_no_decorations_, log_strip_call_site_;
public:
    enum LogLevel { LL_ERROR = 1, LL_WARNING = 2, LL_INFO = 3, LL_DEBUG = 4 };
private:
    LogLevel min_log_level_;
    Logger();
public:
    void redirectOutput(const int new_fd) { fd_ = new_fd; }

    void setMinimumLogLevel(const LogLevel min_log_level) { min_log_level_ = min_log_level; }
    LogLevel getMinimumLogLevel() const { return min_log_level_; }

    //* Emits "msg" and then calls exit(3), also generates a call stack trace if the environment variable BACKTRACE has been set.
    void error(const std::string &msg) __attribute__((noreturn));
    inline void error(const std::string &function_name, const std::string &msg) __attribute__((noreturn))
        { error("in " + function_name + ": " + msg); }

    void warning(const std::string &msg);
    inline void warning(const std::string &function_name, const std::string &msg) { warning("in " + function_name + ": " + msg); }

    void info(const std::string &msg);
    inline void info(const std::string &function_name, const std::string &msg) { info("in " + function_name + ": " + msg); }

    /** \note Only writes actual log messages if the environment variable "UTIL_LOG_DEBUG" exists and is set
     *  to "true"!
     */
    void debug(const std::string &msg);
    inline void debug(const std::string &function_name, const std::string &msg) { debug("in " + function_name + ": " + msg); }

    //* \note Aborts if ""level_candidate" is not one of "ERROR", "WARNING", "INFO" or "DEBUG".
    static LogLevel StringToLogLevel(const std::string &level_candidate);

    // \brief Returns a string representation of "log_level".
    static std::string LogLevelToString(const LogLevel log_level);
private:
    void writeString(const std::string &level, std::string msg);
};
extern Logger *logger;


#define LOG_ERROR(message)   logger->error(__PRETTY_FUNCTION__, message)
#define LOG_WARNING(message) logger->warning(__PRETTY_FUNCTION__, message)
#define LOG_INFO(message)    logger->info(__PRETTY_FUNCTION__, message)
#define LOG_DEBUG(message)   logger->debug(__PRETTY_FUNCTION__, message)


// TestAndThrowOrReturn -- tests condition "cond" and, if it evaluates to "true", throws an exception unless another
//                         exception is already in progress.  In the latter case, TestAndThrowOrReturn() simply
//                         returns.
//
#define TestAndThrowOrReturn(cond, err_text)                                                                       \
    do {                                                                                                           \
        if (unlikely(cond)) {                                                                                      \
            if (unlikely(std::uncaught_exception()))                                                               \
                return;                                                                                            \
            else                                                                                                   \
                throw std::runtime_error(std::string("in ") + __PRETTY_FUNCTION__ + "(" __FILE__ ":"               \
                                         Stringize(__LINE__) "): " + std::string(err_text)                         \
                                         + std::string(errno != 0 ? " (" + std::string(std::strerror(errno)) + ")" \
                                                                         : std::string("")));                      \
            }                                                                                                      \
    } while (false)


/** Must be set to point to argv[0] in main(). */
extern char *progname;


/** \class DSVReader
 *  \brief A "reader" for delimiter-separated values.
 */
class DSVReader {
    char field_separator_;
    char field_delimiter_;
    unsigned line_no_;
    std::string filename_;
    FILE *input_;
public:
    explicit DSVReader(const std::string &filename, const char field_separator=',', const char field_delimiter='"');
    ~DSVReader();
    bool readLine(std::vector<std::string> * const values);
};


#endif // ifndef UTIL_H
