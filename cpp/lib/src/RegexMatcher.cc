/** \file   RegexMatcher.cc
 *  \brief  Implementation of the RegexMatcher class.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2015,2017,2018 Universitätsbibliothek Tübingen.  All rights reserved.
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
#include "RegexMatcher.h"
#include <unordered_map>
#include "Compiler.h"
#include "util.h"


bool RegexMatcher::utf8_configured_;


bool CompileRegex(const std::string &pattern, const unsigned options, ::pcre **pcre_arg,
                  ::pcre_extra **pcre_extra_arg, std::string * const err_msg)
{
    if (err_msg != nullptr)
        err_msg->clear();

    const char *errptr;
    int erroffset;

    int pcre_options(0);
    if (options & RegexMatcher::ENABLE_UTF8)
        pcre_options |= PCRE_UTF8;
    if (options & RegexMatcher::CASE_INSENSITIVE)
        pcre_options |= PCRE_CASELESS;
    if (options & RegexMatcher::MULTILINE)
        pcre_options |= PCRE_MULTILINE;

    *pcre_arg = ::pcre_compile(pattern.c_str(), pcre_options, &errptr, &erroffset, nullptr);
    if (*pcre_arg == nullptr) {
        *pcre_extra_arg = nullptr;
        if (err_msg != nullptr)
            *err_msg = "failed to compile invalid regular expression: \"" + pattern + "\"! ("
                       + std::string(errptr) + ")";
        return false;
    }

    // Can't use PCRE_STUDY_JIT_COMPILE because it's not thread safe.
    *pcre_extra_arg = ::pcre_study(*pcre_arg, 0, &errptr);
    if (*pcre_extra_arg == nullptr and errptr != nullptr) {
        ::pcre_free(*pcre_arg);
        *pcre_arg = nullptr;
        if (err_msg != nullptr)
            *err_msg = "failed to \"study\" the compiled pattern \"" + pattern + "\"! (" + std::string(errptr) + ")";
        return false;
    }

    return true;
}


RegexMatcher *RegexMatcher::RegexMatcherFactory(const std::string &pattern, std::string * const err_msg,
                                                const unsigned options)
{
    // Make sure the PCRE library supports UTF8:
    if ((options & RegexMatcher::ENABLE_UTF8) and not RegexMatcher::utf8_configured_) {
        int utf8_available;
        if (::pcre_config(PCRE_CONFIG_UTF8, reinterpret_cast<void *>(&utf8_available)) == PCRE_ERROR_BADOPTION) {
            if (err_msg != nullptr)
                *err_msg = "PCRE library does not know PCRE_CONFIG_UTF8!";
            return nullptr;
        }

        if (utf8_available != 1) {
            if (err_msg != nullptr)
                *err_msg = "This version of the PCRE library does not support UTF8!";
            return nullptr;
        }

        RegexMatcher::utf8_configured_ = true;
    }

    ::pcre *pcre_ptr;
    ::pcre_extra *pcre_extra_ptr;
    if (not CompileRegex(pattern, options, &pcre_ptr, &pcre_extra_ptr, err_msg)) {
        if (err_msg != nullptr and err_msg->empty())
            *err_msg = "failed to compile pattern: \"" + pattern + "\"";
        return nullptr;
    }

    return new RegexMatcher(pattern, options, pcre_ptr, pcre_extra_ptr);
}


RegexMatcher *RegexMatcher::RegexMatcherFactoryOrDie(const std::string &regex, const unsigned options) {
    std::string error_message;
    RegexMatcher *regex_matcher(RegexMatcher::RegexMatcherFactory(regex, &error_message, options));
    if (regex_matcher == nullptr or not error_message.empty())
        LOG_ERROR("failed to compile regex \"" + regex + "\": " + error_message);

    return regex_matcher;
}


RegexMatcher::RegexMatcher(const RegexMatcher &that): pattern_(that.pattern_) {
    if (this == &that)
        return;

    if (that.pcre_ == nullptr) {
        pcre_ = nullptr;
        pcre_extra_ = nullptr;
    } else {
        std::string err_msg;
        if (not CompileRegex(pattern_, that.options_, &pcre_, &pcre_extra_, &err_msg))
            logger->error("In RegexMatcher copy constructor: unexpected error: " + err_msg);
        substr_vector_    = that.substr_vector_;
        last_match_count_ = that.last_match_count_;
    }
}


RegexMatcher::RegexMatcher(RegexMatcher &&that)
    : pattern_(std::move(that.pattern_)), options_(that.options_), pcre_(that.pcre_),
      pcre_extra_(that.pcre_extra_), last_subject_(std::move(that.last_subject_)),
      substr_vector_(std::move(that.substr_vector_)), last_match_count_(that.last_match_count_)
{
    that.pcre_       = nullptr;
    that.pcre_extra_ = nullptr;
}


bool RegexMatcher::matched(const std::string &subject, const size_t subject_start_offset, std::string * const err_msg,
                           size_t * const start_pos, size_t * const end_pos)
{
    if (err_msg != nullptr)
        err_msg->clear();

    const int retcode(::pcre_exec(pcre_, pcre_extra_, subject.data(), subject.length(), subject_start_offset, 0,
                                    &substr_vector_[0], substr_vector_.size()));

    if (retcode == 0) {
        if (err_msg != nullptr)
            *err_msg = "Too many captured substrings! (We only support "
                       + std::to_string(substr_vector_.size() / 3 - 1) + " substrings.)";
        return false;
    }

    if (retcode > 0) {
        last_match_count_ = retcode;
        last_subject_     = subject;
        if (start_pos != nullptr)
            *start_pos = substr_vector_[0];
        if (end_pos != nullptr)
            *end_pos = substr_vector_[1];
        return true;
    }

    if (retcode != PCRE_ERROR_NOMATCH) {
        if (retcode == PCRE_ERROR_BADUTF8) {
            if (err_msg != nullptr)
                *err_msg = "A \"subject\" with invalid UTF-8 was passed into RegexMatcher::matched()!";
        } else if (err_msg != nullptr)
            *err_msg = "Unknown error!";
    }

    return false;
}


std::string RegexMatcher::replaceAll(const std::string &subject, const std::string &replacement) {
    if (not matched(subject))
        return subject;

    std::string replaced_string;
    // the matches need to be sequentially sorted from left to right
    size_t subject_start_offset(0), match_start_offset(0), match_end_offset(0);
    while (subject_start_offset < subject.length() and
           matched(subject, subject_start_offset, /* err_msg */ nullptr, &match_start_offset, &match_end_offset))
    {
        replaced_string += subject.substr(subject_start_offset, match_start_offset - subject_start_offset);
        replaced_string += replacement;
        subject_start_offset = match_end_offset;
    }

    return replaced_string;
}


bool RegexMatcher::Matched(const std::string &regex, const std::string &subject, const unsigned options,
                           std::string * const err_msg, size_t * const start_pos, size_t * const end_pos)
{
    static std::unordered_map<std::string, RegexMatcher *> regex_to_matcher_map;
    const std::string KEY(regex + ":" + std::to_string(options));
    const auto regex_and_matcher(regex_to_matcher_map.find(KEY));
    if (regex_and_matcher != regex_to_matcher_map.cend())
        return regex_and_matcher->second->matched(subject, err_msg, start_pos, end_pos);

    RegexMatcher * const matcher(RegexMatcher::RegexMatcherFactory(regex, err_msg, options));
    if (matcher == nullptr)
        LOG_ERROR("Failed to compile pattern \"" + regex + "\": " + *err_msg);
    regex_to_matcher_map[KEY] = matcher;

    return matcher->matched(subject, err_msg, start_pos, end_pos);
}


std::string RegexMatcher::operator[](const unsigned group) const {
    if (unlikely(group >= last_match_count_))
        throw std::out_of_range("in RegexMatcher::operator[]: group(" + std::to_string(group) + ") >= "
                                + std::to_string(last_match_count_) + "!");

    const unsigned first_index(group * 2);
    const unsigned substring_length(substr_vector_[first_index + 1] - substr_vector_[first_index]);
    return (substring_length == 0) ? "" : last_subject_.substr(substr_vector_[first_index], substring_length);
}
