/** \file    MiscUtil.cc
 *  \brief   Implementation of miscellaneous utility functions.
 *  \author  Dr. Johannes Ruscheinski
 *  \author  Dr. Gordon W. Paynter
 */

/*
 *  Copyright 2002-2008 Project iVia.
 *  Copyright 2002-2008 The Regents of The University of California.
 *  Copyright 2016-2018 Universitätsbibliothek Tübingen
 *
 *  This file is part of the libiViaCore package.
 *
 *  The libiViaCore package is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public License as
 *  published by the Free Software Foundation; either version 2 of the License,
 *  or (at your option) any later version.
 *
 *  libiViaCore is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public License
 *  along with libiViaCore; if not, write to the Free Software Foundation, Inc.,
 *  59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

#include "MiscUtil.h"
#include <map>
#include <queue>
#include <set>
#include <stdexcept>
#include <unordered_set>
#include <cctype>
#include <cxxabi.h>
#include <execinfo.h>
#include <unistd.h>
#include "BSZUtil.h"
#include "Compiler.h"
#include "FileUtil.h"
#include "RegexMatcher.h"
#include "StringUtil.h"
#include "util.h"


namespace MiscUtil {


char HexDigit(const unsigned value) {
    switch (value) {
    case 0:
        return '0';
    case 1:
        return '1';
    case 2:
        return '2';
    case 3:
        return '3';
    case 4:
        return '4';
    case 5:
        return '5';
    case 6:
        return '6';
    case 7:
        return '7';
    case 8:
        return '8';
    case 9:
        return '9';
    case 0xA:
        return 'A';
    case 0xB:
        return 'B';
    case 0xC:
        return 'C';
    case 0xD:
        return 'D';
    case 0xE:
        return 'E';
    case 0xF:
        return 'F';
    default:
        logger->error("in MiscUtil::HexDigit: invalid value " + std::to_string(value) + "!");
    }
}


static char HEX_DIGITS[] = "0123456789aAbBcCdDeEfF";


bool IsHexDigit(const char ch) {
    return std::strchr(HEX_DIGITS, ch) != nullptr;
}


char GeneratePPNChecksumDigit(const std::string &ppn_without_checksum_digit) {
    if (unlikely(ppn_without_checksum_digit.length() != 8 and ppn_without_checksum_digit.length() != 9))
        throw std::runtime_error("in MiscUtil::GeneratePPNChecksumDigit: argument's length is neither 8 nor 9!");

    unsigned checksum(0);
    for (unsigned i(0); i < ppn_without_checksum_digit.length(); ++i)
        checksum += (9 - i) * (ppn_without_checksum_digit[i] - '0');
    checksum = (11 - (checksum % 11)) % 11;

    return checksum == 10 ? 'X' : '0' + checksum;
}


bool IsValidPPN(const std::string &ppn_candidate) {
    if (ppn_candidate.length() != BSZUtil::PPN_LENGTH_OLD and ppn_candidate.length() != BSZUtil::PPN_LENGTH_NEW)
        return false;

    for (unsigned i(0); i < ppn_candidate.length() - 1; ++i) {
        if (not StringUtil::IsDigit(ppn_candidate[i]))
            return false;
    }

    return ppn_candidate[ppn_candidate.length() - 1]
           == GeneratePPNChecksumDigit(ppn_candidate.substr(0, ppn_candidate.length() - 1));
}


std::string GetEnv(const char * const name) {
    const char * const value(::getenv(name));
    if (value == nullptr)
        throw std::runtime_error("in MiscUtil::GetEnv: ::getenv(\"" + std::string(name) + "\") failed!");

    return value;
}


std::string SafeGetEnv(const char * const name) {
    const char * const value(::getenv(name));
    return value == nullptr ? "" : value;
}


void SetEnv(const std::string &name, const std::string &value, const bool overwrite) {
    if (unlikely(::setenv(name.c_str(), value.c_str(), overwrite ? 1 : 0) != 0))
        throw std::runtime_error("in MiscUtil::SetEnv: setenv(3) failed!");
}


enum EscapeState { NOT_ESCAPED, SINGLE_QUOTED, DOUBLE_QUOTED };


// Helper for ParseLine(),
static std::string ExtractBourneString(std::string::const_iterator &ch, const std::string::const_iterator &end,
                                       const char barrier)
{
    std::string value;

    bool backslash_seen(false);
    EscapeState state(NOT_ESCAPED);
    for (;;) {
        if (ch == end)
            return value;

        if (state == NOT_ESCAPED) {
            if (backslash_seen) {
                value += *ch;
                backslash_seen = false;
            } else if (*ch == '\'')
                state = SINGLE_QUOTED;
            else if (*ch == '"')
                state = DOUBLE_QUOTED;
            else if (*ch == '\\')
                backslash_seen = true;
            else if (*ch == barrier)
                return value;
            else
                value += *ch;
        } else if (state == SINGLE_QUOTED) {
            if (*ch == '\'')
                state = NOT_ESCAPED;
            else
                value += *ch;
        } else if (state == DOUBLE_QUOTED) {
            if (backslash_seen) {
                if (*ch != '"' and *ch != '\\')
                    value += '\\';
                value += *ch;
                backslash_seen = false;
            } else if (*ch == '\\')
                backslash_seen = true;
            else if (*ch == '"')
                state = NOT_ESCAPED;
            else
                value += *ch;
        }

        ++ch;
    }

    return value;
}


static bool ExportsParseLine(std::string line, std::string * const key, std::string * const value) {
    key->clear(), value->clear();

    StringUtil::TrimWhite(&line);
    if (not StringUtil::StartsWith(line, "export"))
        return true;

    // Remove leading "export":
    line = line.substr(__builtin_strlen("export"));

    StringUtil::TrimWhite(&line);
    auto ch(line.cbegin());
    *key = ExtractBourneString(ch, line.cend(), '=');
    if (key->empty())
        return false;
    ++ch;
    *value = ExtractBourneString(ch, line.cend(), '#');
    return true;
}


void LoadExports(const std::string &path, const bool overwrite) {
    std::unique_ptr<File> input(FileUtil::OpenInputFileOrDie(path));
    unsigned line_no(0);
    while (not input->eof()) {
        ++line_no;

        std::string line;
        input->getline(&line);
        std::string key, value;
        if (not ExportsParseLine(line, &key, &value))
            LOG_ERROR("failed to parse an export statement on line #" + std::to_string(line_no) + " in \"" + input->getPath()
                  + "\"!");
        if (not key.empty())
            SetEnv(key, value, overwrite);
    }
}



bool EnvironmentVariableExists(const std::string &name) {
    const char * const value(::getenv(name.c_str()));
    return value != nullptr;
}


std::string GetUserName() {
    char username[200];
    if (unlikely(::getlogin_r(username, sizeof username) != 0))
        return "*unknown user* [" + std::string(::strerror(errno)) + "]";
    return username;
}


bool IsDOI(const std::string &doi_candidate) {
    static RegexMatcher * const matcher(RegexMatcher::RegexMatcherFactory("^(10[.][0-9]{4,}(?:[.][0-9]+)*/(?:(?![\"&\\'<>])\\S)+)$"));
    return matcher->matched(doi_candidate);
}


bool IsPossibleISSN(std::string issn_candidate) {
    if (issn_candidate.length() != 8 and issn_candidate.length() != 9)
        return false;
    if (issn_candidate.length() == 9) {
        if (issn_candidate[4] != '-')
            return false;
        issn_candidate = issn_candidate.substr(0, 4) + issn_candidate.substr(5, 4); // Remove hyphen.
    }

    //
    // For an explanation of how to determine the checksum digit, have a look at
    // https://en.wikipedia.org/wiki/International_Standard_Serial_Number#Code_format&oldid=767018094
    //

    unsigned sum(0), position(8);
    for (unsigned i(0); i < 7; ++i) {
        const char ch(issn_candidate[i]);
        if (not StringUtil::IsDigit(ch))
            return false;
        sum += position * (ch - '0');
        --position;
    }
    const unsigned modulus(sum % 11);

    char check_digit;
    if (modulus == 0)
        check_digit = '0';
    else {
        unsigned digit(11 - modulus);
        if (digit == 10)
            check_digit = 'X';
        else
            check_digit = '0' + digit;
    }

    return std::toupper(issn_candidate[7]) == check_digit;
}


bool NormaliseISSN(const std::string &issn_candidate, std::string * const normalised_issn) {
    if (issn_candidate.length() == 9) {
        *normalised_issn = issn_candidate;
        return true;
    }

    if (issn_candidate.length() == 8) {
        *normalised_issn = issn_candidate.substr(0, 4) + '-' + issn_candidate.substr(4, 4);
        return true;
    }

    return false;
}


std::string StringMapToString(const std::map<std::string, std::string> &map) {
    std::string map_as_string;
    for (const auto &key_and_value : map)
        map_as_string += key_and_value.first + "=" + key_and_value.second + ", ";

    return map_as_string.empty() ? "[]" : "[" + map_as_string.substr(0, map_as_string.length() - 2) + "]";
}


static unsigned GetLogSuffix(const std::string &log_file_prefix, const std::string &filename) {
    if (filename == log_file_prefix)
        return 0;

    unsigned generation;
    if (unlikely(not StringUtil::ToUnsigned(filename.substr(log_file_prefix.length() + 1), &generation)))
        logger->error("in GetLogSuffix(MiscUtil.cc): bad conversion, filename = \"" + filename + "\"!");

    return generation;
}


class LogCompare {
    const std::string log_file_prefix_;
public:
    explicit LogCompare(const std::string &log_file_prefix) : log_file_prefix_(log_file_prefix) { }
    bool operator()(const std::string &filename1, const std::string &filename2)
        { return GetLogSuffix(log_file_prefix_, filename1) < GetLogSuffix(log_file_prefix_, filename2); }
};


static std::string IncrementFile(const std::string &log_file_prefix, const std::string &filename) {
    if (filename == log_file_prefix)
        return log_file_prefix + ".1";

    return log_file_prefix + "." + std::to_string(GetLogSuffix(log_file_prefix, filename) + 1);
}


void LogRotate(const std::string &log_file_prefix, const unsigned max_count) {
    std::string dirname, basename;
    FileUtil::DirnameAndBasename(log_file_prefix, &dirname, &basename);
    if (basename.empty()) {
        basename = dirname;
        dirname  = ".";
    }
    if (dirname.empty())
        dirname = ".";

    std::vector<std::string> filenames;
    FileUtil::Directory directory(dirname, "^" + basename + "(\\.[0-9]+)?$");
    for (const auto entry : directory) {
        if (entry.getType() == DT_REG)
            filenames.emplace_back(entry.getName());;
    }

    std::sort(filenames.begin(), filenames.end(), LogCompare(basename));

    if (max_count > 0) {
        while (filenames.size() > max_count) {
            const std::string path_to_delete(dirname + "/" + filenames.back());
            if (unlikely(not FileUtil::DeleteFile(path_to_delete)))
                logger->error("in MiscUtil::LogRotate: failed to delete \"" + path_to_delete + "\"!");
            filenames.pop_back();
        }
    }

    for (auto filename(filenames.rbegin()); filename != filenames.rend(); ++filename) {
        if (unlikely(not FileUtil::RenameFile(dirname + "/" + *filename,
                                              dirname + "/" + IncrementFile(basename, *filename))))
            logger->error("in MiscUtil::LogRotate:: failed to rename \"" + dirname + "/" + *filename + "\" to \""
                          + dirname + "/" + IncrementFile(basename, *filename) + "\"!");
    }
}


bool TopologicalSort(const std::vector<std::pair<unsigned, unsigned>> &edges, std::vector<unsigned> * const node_order) {
    std::unordered_set<unsigned> nodes;
    int max_node(-1);
    for (const auto &edge : edges) {
        nodes.emplace(edge.first);
        if (static_cast<int>(edge.first) > max_node)
            max_node = edge.first;
        nodes.emplace(edge.second);
        if (static_cast<int>(edge.second) > max_node)
            max_node = edge.second;
    }
    if (max_node != static_cast<int>(nodes.size() - 1))
        logger->error("in MiscUtil::TopologicalSort: we don't have the required 0..N-1 labelling of nodes!");

    std::vector<std::vector<unsigned>> neighbours(nodes.size());
    std::vector<unsigned> indegrees(nodes.size());
    for (const auto &edge : edges) {
        neighbours[edge.first].emplace_back(edge.second);
        ++indegrees[edge.second];
    }

    // Enqueue all nodes with no incident edges:
    std::queue<unsigned> queue;
    for (unsigned node(0); node < nodes.size(); ++node) {
        if (indegrees[node] == 0)
            queue.push(node);
    }

    unsigned visited_node_count(0);
    while (not queue.empty()) {
        const unsigned current_node(queue.front());
        node_order->emplace_back(current_node);
        queue.pop();

        for (auto neighbour : neighbours[current_node]) {
            if (--indegrees[neighbour] == 0)
                queue.push(neighbour);
        }

        ++visited_node_count;
    }

    return visited_node_count == nodes.size(); // If this is nor true we have at least one cycle!
}


std::vector<std::string> GetCallStack() {
    std::vector<std::string> call_stack;

    const int MAX_ADDR_COUNT(100);
    char buffer[MAX_ADDR_COUNT * sizeof(void *)];
    const int address_count(::backtrace((void **)buffer, MAX_ADDR_COUNT));
    char **symbols(backtrace_symbols(reinterpret_cast<void **>(buffer), address_count));
    for (int addr_no(0); addr_no < address_count; ++addr_no) {
        char *symbol_start(std::strchr(symbols[addr_no], '('));
        if (symbol_start == nullptr)
            continue;
        ++symbol_start; // Skip over the opening parenthesis.
        // Symbols end at a plus sign which is followed by an address.
        char *plus(std::strchr(symbol_start, '+'));
        if (plus == nullptr)
            continue;
        *plus = '\0';
        int status;
        char *demangled_name(abi::__cxa_demangle(symbol_start, nullptr, nullptr, &status));
        if (status == 0)
            call_stack.emplace_back(demangled_name);
        ::free(reinterpret_cast<void *>(demangled_name));
    }
    ::free(reinterpret_cast<void *>(symbols));

    return call_stack;
}


static bool ParseLine(const std::string &line, std::string * const key, std::string * const value) {
    key->clear(), value->clear();

    // Extract the key:
    auto ch(line.cbegin());
    while (ch != line.cend() and *ch != '=') {
        if (unlikely(*ch == '\\')) {
            ++ch;
            if (unlikely(ch == line.cend()))
                return false;
        }
        *key += *ch++;
    }
    if (unlikely(ch == line.cend()))
        return false;
    ++ch; // Skip over the equal-sign.

    // Extract value:
    while (ch != line.cend() and *ch != '#' /* Comment start. */) {
        if (unlikely(*ch == '\\')) {
            ++ch;
            if (unlikely(ch == line.cend()))
                return false;
        }
        *value += *ch++;
    }
    StringUtil::RightTrim(value);

    return not key->empty() and not value->empty();
}


size_t LoadMapFile(const std::string &filename, std::unordered_map<std::string, std::string> * const from_to_map) {
    std::unique_ptr<File> input(FileUtil::OpenInputFileOrDie(filename));

    unsigned line_no(0);
    while (not input->eof()) {
        std::string line(input->getline());
        ++line_no;

        StringUtil::Trim(&line);
        std::string key, value;
        if (not ParseLine(line, &key, &value))
            LOG_ERROR("invalid input on line \"" + std::to_string(line_no) + "\" in \"" + input->getPath() + "\"!");
        from_to_map->emplace(key, value);
    }

    return from_to_map->size();
}


std::string MakeOrdinal(const unsigned number) {
    if (number % 10 == 1)
        return StringUtil::ToString(number) + "st";
    if (number % 10 == 2)
        return StringUtil::ToString(number) + "nd";
    if (number % 10 == 3)
        return StringUtil::ToString(number) + "rd";
    return StringUtil::ToString(number) + "th";    
}


} // namespace MiscUtil
