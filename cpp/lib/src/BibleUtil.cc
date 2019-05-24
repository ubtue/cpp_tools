/** \file   BibleUtil.cc
 *  \brief  Implementation of a bible reference parser that generates numeric code ranges.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2014-2017,2019 Universitätsbibliothek Tübingen.  All rights reserved.
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
#include "BibleUtil.h"
#include <iostream>
#include <cctype>
#include "Locale.h"
#include "MapUtil.h"
#include "RegexMatcher.h"
#include "StringUtil.h"
#include "TextUtil.h"
#include "util.h"


namespace BibleUtil {


namespace {


// Checks whether the new reference comes strictly after already existing references.
bool NewReferenceIsCompatibleWithExistingReferences(
        const std::pair<std::string, std::string> &new_ref,
        const std::set<std::pair<std::string, std::string>> &existing_refs)
{
    for (const auto existing_ref : existing_refs) {
        if (new_ref.first <= existing_ref.second)
            return false;
    }

    return true;
}


bool IsNumericString(const std::string &s) {
    for (const char ch : s) {
        if (not StringUtil::IsDigit(ch))
            return false;
    }

    return true;
}


bool ReferenceIsWellFormed(const std::string &bib_ref_candidate) {
    if (bib_ref_candidate.length() != BOOK_CODE_LENGTH + MAX_CHAPTER_LENGTH + MAX_VERSE_LENGTH)
        return false;

    for (const char ch : bib_ref_candidate) {
        if (not StringUtil::IsDigit(ch))
            return false;
    }

    return true;
}


bool RangesAreWellFormed(const std::set<std::pair<std::string, std::string>> &ranges) {
    for (const auto &range : ranges) {
        if (not ReferenceIsWellFormed(range.first) or not ReferenceIsWellFormed(range.second))
            return false;
    }

    return true;
}


std::string RangesToString(const std::set<std::pair<std::string, std::string>> &ranges) {
    std::string ranges_as_string;
    for (const auto &range : ranges) {
        if (not ranges_as_string.empty())
            ranges_as_string += ", ";
        ranges_as_string += range.first + ":" + range.second;
    }

    return ranges_as_string;
}


bool ParseRefWithDot(const std::string &bib_ref_candidate, const std::string &book_code,
                     std::set<std::pair<std::string, std::string>> * const start_end)
{
    std::set<std::pair<std::string, std::string>> new_start_end;

    size_t comma_or_colon_pos(bib_ref_candidate.find(','));
    if (comma_or_colon_pos == std::string::npos)
        comma_or_colon_pos = bib_ref_candidate.find(':');
    if (comma_or_colon_pos == std::string::npos) // We must have a comma or a colon!
        return false;

    const std::string chapter(StringUtil::PadLeading(bib_ref_candidate.substr(0, comma_or_colon_pos),
                                                     MAX_CHAPTER_LENGTH, '0'));
    if (chapter.length() != MAX_CHAPTER_LENGTH or not IsNumericString(chapter))
        return false;

    const std::string rest(bib_ref_candidate.substr(comma_or_colon_pos + 1));
    bool in_verse1(true);
    std::string verse1, verse2;
    for (const char ch : rest) {
        if (StringUtil::IsDigit(ch)) {
            if (in_verse1) {
                verse1 += ch;
                if (verse1.length() > MAX_VERSE_LENGTH)
                    return false;
            } else {
                verse2 += ch;
                if (verse2.length() > MAX_VERSE_LENGTH)
                    return false;
            }
        } else if (ch == '.') {
            if (in_verse1) {
                if (verse1.empty())
                    return false;
                verse1 = StringUtil::PadLeading(verse1, MAX_VERSE_LENGTH, '0');
                const std::pair<std::string, std::string> new_reference(
                    std::make_pair(book_code + chapter + verse1, book_code + chapter + verse1));
                if (not NewReferenceIsCompatibleWithExistingReferences(new_reference, new_start_end))
                    return false;
                new_start_end.insert(new_reference);
                verse1.clear();
            } else {
                if (verse2.empty())
                    return false;
                verse2 = StringUtil::PadLeading(verse2, MAX_VERSE_LENGTH, '0');
                if (verse2 <= verse1)
                    return false;
                const std::pair<std::string, std::string> new_reference(
                    std::make_pair(book_code + chapter + verse1, book_code + chapter + verse2));
                if (not NewReferenceIsCompatibleWithExistingReferences(new_reference, new_start_end))
                    return false;
                new_start_end.insert(new_reference);
                verse1.clear();
                verse2.clear();
                in_verse1 = true;
            }
        } else if (ch == '-') {
            if (not in_verse1 or verse1.empty())
                return false;
            verse1 = StringUtil::PadLeading(verse1, MAX_VERSE_LENGTH, '0');
            in_verse1 = false;
        } else if (islower(ch)) {
            if (in_verse1) {
                if (verse1.empty())
                    return false;
                verse1 = StringUtil::PadLeading(verse1, MAX_VERSE_LENGTH, '0');
            } else {
                if (verse2.empty())
                    return false;
                verse2 = StringUtil::PadLeading(verse2, MAX_VERSE_LENGTH, '0');
            }
        } else
            return false;
    }

    if (in_verse1) {
        if (verse1.empty())
            return false;
        verse1 = StringUtil::PadLeading(verse1, MAX_VERSE_LENGTH, '0');
        const std::pair<std::string, std::string> new_reference(
            std::make_pair(book_code + chapter + verse1, book_code + chapter + verse1));
        if (not NewReferenceIsCompatibleWithExistingReferences(new_reference, new_start_end))
            return false;
        new_start_end.insert(new_reference);
    } else {
        if (verse2.empty())
            return false;
        verse2 = StringUtil::PadLeading(verse2, MAX_VERSE_LENGTH, '0');
        if (verse2 <= verse1)
            return false;
        const std::pair<std::string, std::string> new_reference(
            std::make_pair(book_code + chapter + verse1, book_code + chapter + verse2));
        if (not NewReferenceIsCompatibleWithExistingReferences(new_reference, new_start_end))
            return false;
        new_start_end.insert(new_reference);
    }

    start_end->insert(new_start_end.cbegin(), new_start_end.cend());
    return true;
}


enum State { INITIAL, CHAPTER1, CHAPTER2, VERSE1, VERSE2 };


} // unnamed namespace


bool ParseBibleReference(std::string bib_ref_candidate, const std::string &book_code,
                         std::set<std::pair<std::string, std::string>> * const start_end)
{
    StringUtil::RemoveChars(" \t", &bib_ref_candidate); // Remove embedded spaces and tabs.
    if (bib_ref_candidate.empty()) {
        start_end->insert(std::make_pair(book_code + std::string(MAX_CHAPTER_LENGTH + MAX_VERSE_LENGTH, '0'),
                                         book_code + std::string(MAX_CHAPTER_LENGTH + MAX_VERSE_LENGTH, '9')));
        return true;
    }

    const Locale c_locale("C", LC_ALL); // We don't want islower() to accept characters w/ diacritical marks!

    if (bib_ref_candidate.find('.') != std::string::npos) {
        const bool parse_succeeded(ParseRefWithDot(bib_ref_candidate, book_code, start_end));
        if (parse_succeeded and not RangesAreWellFormed(*start_end))
            logger->error("Bad ranges (" + RangesToString(*start_end) + ") were generated in ParseBibleReference! (1)");
        return parse_succeeded;
    }

    State state(INITIAL);
    std::string accumulator, chapter1, verse1, chapter2, verse2;
    for (auto ch(bib_ref_candidate.cbegin()); ch != bib_ref_candidate.cend(); ++ch) {
        switch (state) {
        case INITIAL:
            if (StringUtil::IsDigit(*ch)) {
                accumulator += *ch;
                state = CHAPTER1;
            } else
                return false;
            break;
        case CHAPTER1:
            if (StringUtil::IsDigit(*ch)) {
                accumulator += *ch;
                if (accumulator.length() > MAX_CHAPTER_LENGTH)
                    return false;
            } else if (*ch == '-') {
                chapter1 = StringUtil::PadLeading(accumulator, MAX_CHAPTER_LENGTH, '0');
                accumulator.clear();
                state = CHAPTER2;
            } else if (*ch == ',' or *ch == ':') {
                chapter1 = StringUtil::PadLeading(accumulator, MAX_CHAPTER_LENGTH, '0');
                accumulator.clear();
                state = VERSE1;
            } else
                return false;
            break;
        case VERSE1:
            if (StringUtil::IsDigit(*ch)) {
                accumulator += *ch;
                if (accumulator.length() > MAX_VERSE_LENGTH)
                    return false;
            } else if (islower(*ch)) {
                if (accumulator.empty())
                    return false;
                accumulator = StringUtil::PadLeading(accumulator, MAX_VERSE_LENGTH, '0');
                // Ignore this non-standardised letter!
            } else if (*ch == '-') {
                if (accumulator.empty())
                    return false;
                verse1 = StringUtil::PadLeading(accumulator, MAX_VERSE_LENGTH, '0');
                accumulator.clear();

                // We need to differentiate between a verse vs. a chapter-hyphen:
                const std::string remainder(bib_ref_candidate.substr(ch - bib_ref_candidate.cbegin()));
                if (remainder.find(',') == std::string::npos and remainder.find(':') == std::string::npos) // => We have a verse hyphen!
                    state = VERSE2;
                else
                    state = CHAPTER2;
            } else
                return false;
            break;
        case CHAPTER2:
            if (StringUtil::IsDigit(*ch)) {
                accumulator += *ch;
                if (accumulator.length() > MAX_CHAPTER_LENGTH)
                    return false;
            } else if (*ch == ',' or *ch == ':') {
                if (accumulator.empty())
                    return false;
                chapter2 = StringUtil::PadLeading(accumulator, MAX_CHAPTER_LENGTH, '0');
                accumulator.clear();
                state = VERSE2;
            } else
                return false;
            break;
        case VERSE2:
            if (StringUtil::IsDigit(*ch)) {
                accumulator += *ch;
                if (accumulator.length() > MAX_VERSE_LENGTH)
                    return false;
            } else if (islower(*ch)) {
                if (accumulator.empty())
                    return false;
                accumulator = StringUtil::PadLeading(accumulator, MAX_VERSE_LENGTH, '0');
                // Ignore this non-standardised letter!
            } else
                return false;
            break;
        }
    }

    if (state == CHAPTER1) {
        chapter1 = book_code + StringUtil::PadLeading(accumulator, MAX_CHAPTER_LENGTH, '0');
        start_end->insert(std::make_pair(chapter1 + std::string(MAX_VERSE_LENGTH, '0'),
                                         chapter1 + std::string(MAX_VERSE_LENGTH, '9')));
    } else if (state == CHAPTER2) {
        if (accumulator.empty())
            return false;
        verse1 = StringUtil::PadLeading(verse1, MAX_VERSE_LENGTH, '0');
        verse2 = verse2.empty() ? std::string(MAX_VERSE_LENGTH, '9')
                                : StringUtil::PadLeading(verse2, MAX_VERSE_LENGTH, '0');
        const std::string chapter1_verse1(chapter1 + verse1);
        const std::string chapter2_verse2(StringUtil::PadLeading(accumulator, MAX_CHAPTER_LENGTH, '0') + verse2);
        if (chapter2_verse2 <= chapter1_verse1)
            return false;
        start_end->insert(std::make_pair(book_code + chapter1_verse1, book_code + chapter2_verse2));
    } else if (state == VERSE1) {
        verse1 = StringUtil::PadLeading(accumulator, MAX_VERSE_LENGTH, '0');
        accumulator = book_code + chapter1 + verse1;
        start_end->insert(std::make_pair(accumulator, accumulator));
    } else if (state == VERSE2) {
        if (accumulator.empty())
            return false;
        verse1 = StringUtil::PadLeading(verse1, MAX_VERSE_LENGTH, '0');
        verse2 = StringUtil::PadLeading(accumulator, MAX_VERSE_LENGTH, '0');
        const std::string start(book_code + chapter1 + verse1);
        const std::string end(book_code + (chapter2.empty() ? chapter1 : chapter2) + verse2);
        if (end <= start)
            return false;
        start_end->insert(std::make_pair(start, end));
    }

    if (not RangesAreWellFormed(*start_end))
        logger->error("Bad ranges (" + RangesToString(*start_end) + ") were generated in ParseBibleReference! (2)");
    return true;
}


bool CanParseBibleReference(const std::string &bib_ref_candidate) {
    std::set<std::pair<std::string, std::string>> start_end;
    return ParseBibleReference(bib_ref_candidate, std::string(BOOK_CODE_LENGTH, '0'), &start_end);
}


// Squeezes out spaces after a leading number, e.g. "1. mos" => "1.mos" or "1 mos" => "1mos".
static std::string CanoniseLeadingNumber(const std::string &bible_reference_candidate) {
    static RegexMatcher * const matcher(RegexMatcher::RegexMatcherFactory("^\\d\\.?\\s+\\S+"));
    std::string err_msg;
    if (not matcher->matched(bible_reference_candidate, &err_msg)) {
        if (not err_msg.empty())
            logger->error("unexpected reg ex error: " + err_msg);
        return bible_reference_candidate;
    }

    std::string ordinal_string;
    ordinal_string = bible_reference_candidate[0];
    size_t rest_start(1);
    if (bible_reference_candidate[1] == '.') {
        ordinal_string += '.';
        ++rest_start;
    }

    while (isspace(bible_reference_candidate[rest_start]))
        ++rest_start;

    return ordinal_string + bible_reference_candidate.substr(rest_start);
}


static std::string InsertSpaceAtFirstLetterDigitBoundary(const std::string &s) {
    if (s.empty())
        return s;

    std::string retval;
    bool found_first_boundary(false);
    auto ch(s.cbegin());
    retval += *ch;
    while (++ch != s.cend()) {
        if (not found_first_boundary and (std::isalpha(*(ch - 1)) and std::isdigit(*ch))) {
            found_first_boundary = true;
            retval += ' ';
        }

        retval += *ch;
    }

    return retval;
}


static bool SplitIntoBookAndChaptersAndVerses(const std::string &bible_reference_candidate, std::string * const book_candidate,
                                              std::string * const chapters_and_verses_candidate)
{
    std::string normalised_bible_reference_candidate(CanoniseLeadingNumber(InsertSpaceAtFirstLetterDigitBoundary(
        StringUtil::RemoveChars(" \t", bible_reference_candidate))));
    const size_t len(normalised_bible_reference_candidate.length());
    if (len <= 3)
        *book_candidate = normalised_bible_reference_candidate;
    else if (isdigit(normalised_bible_reference_candidate[len - 1])
             or (isalpha(normalised_bible_reference_candidate[len - 1])
                 and isdigit(normalised_bible_reference_candidate[len - 2])))
    {
        const size_t last_space_pos(normalised_bible_reference_candidate.rfind(' '));
        if (last_space_pos == std::string::npos)
            *book_candidate = normalised_bible_reference_candidate;
        else {
            *book_candidate = normalised_bible_reference_candidate.substr(0, last_space_pos);
            *chapters_and_verses_candidate = normalised_bible_reference_candidate.substr(last_space_pos + 1);
        }
    } else
        *book_candidate = normalised_bible_reference_candidate;

    return not book_candidate->empty();
}


bool SplitIntoBooksAndChaptersAndVerses(const std::string &bible_reference_query,
                                        std::vector<std::string> * const book_candidates,
                                        std::vector<std::string> * const chapters_and_verses_candidates)
{
    book_candidates->clear();
    chapters_and_verses_candidates->clear();

    std::vector<std::string> bible_reference_candidates;

    static const std::string OR(" OR ");
    size_t start_pos(0), found_pos, last_found_pos;
    while ((found_pos = StringUtil::FindCaseInsensitive(bible_reference_query, OR, start_pos)) != std::string::npos) {
        last_found_pos = found_pos;
        bible_reference_candidates.emplace_back(bible_reference_query.substr(start_pos, found_pos - start_pos));
        start_pos = found_pos + OR.length();
    }
    if (bible_reference_candidates.empty())
        bible_reference_candidates.emplace_back(bible_reference_query);
    else
        #ifndef __clang__
        #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
        #endif
        bible_reference_candidates.emplace_back(bible_reference_query.substr(last_found_pos + OR.length()));
        #ifndef __clang__
        #pragma GCC diagnostic error "-Wmaybe-uninitialized"
        #endif

    for (const auto &bible_reference_candidate : bible_reference_candidates) {
        book_candidates->resize(book_candidates->size() + 1);
        chapters_and_verses_candidates->resize(chapters_and_verses_candidates->size() + 1);
        if (not SplitIntoBookAndChaptersAndVerses(bible_reference_candidate, &book_candidates->back(),
                                                  &chapters_and_verses_candidates->back()))
            return false;
    }

    return true;
}


BibleBookCanoniser::BibleBookCanoniser(const std::string &books_of_the_bible_to_canonical_form_map_filename) {
    MapUtil::DeserialiseMap(books_of_the_bible_to_canonical_form_map_filename,
                            &books_of_the_bible_to_canonical_form_map_);
}


std::string BibleBookCanoniser::canonise(const std::string &bible_book_candidate, const bool verbose) const {
    const auto non_canonical_form_and_canonical_form(
        books_of_the_bible_to_canonical_form_map_.find(bible_book_candidate));
    if (non_canonical_form_and_canonical_form != books_of_the_bible_to_canonical_form_map_.end()) {
        if (verbose)
            std::cerr << "Replacing \"" << bible_book_candidate << "\" with \""
                      << non_canonical_form_and_canonical_form->second << "\".\n";
        return non_canonical_form_and_canonical_form->second;
    }

    return bible_book_candidate;
}


BibleBookToCodeMapper::BibleBookToCodeMapper(const std::string &books_of_the_bible_to_code_map_filename) {
    MapUtil::DeserialiseMap(books_of_the_bible_to_code_map_filename, &bible_books_to_codes_map_);
}


std::string BibleBookToCodeMapper::mapToCode(const std::string &bible_book_candidate, const bool verbose) const {
    const auto bible_book_and_code(bible_books_to_codes_map_.find(bible_book_candidate));
    if (bible_book_and_code == bible_books_to_codes_map_.end()) {
        if (verbose)
            std::cerr << "No mapping from \"" << bible_book_candidate << "\" to a book code was found!\n";

        return ""; // Unknown bible book!
    }

    return bible_book_and_code->second;
}


BibleAliasMapper::BibleAliasMapper(const std::string &bible_aliases_map_filename) {
    MapUtil::DeserialiseMap(bible_aliases_map_filename, &aliases_to_canonical_forms_map_);
}


// 6 Esra is a virtual bible book that corresponds to 4 Esra 15-16.
std::string Map6Esra(const std::string &bible_reference_candidate) {
    std::string book_candidate, chapters_and_verses_candidate;
    SplitIntoBookAndChaptersAndVerses(bible_reference_candidate, &book_candidate, &chapters_and_verses_candidate);
    if (chapters_and_verses_candidate.empty())
        return "4esra15-16";

    auto iter(chapters_and_verses_candidate.cbegin());
    std::string chapter_digits;
    while (StringUtil::IsDigit(*iter))
        chapter_digits += *iter++;

    if (unlikely(chapter_digits.empty()))
        return bible_reference_candidate; // We give up.

    return "4esra" + std::to_string(StringUtil::ToUnsigned(chapter_digits) + 14)
           + chapters_and_verses_candidate.substr(chapter_digits.length());
}


// 5 Esra is a virtual bible book that corresponds to 4 Esra 1-2.
std::string Map5Esra(const std::string &bible_reference_candidate) {
    std::string book_candidate, chapters_and_verses_candidate;
    SplitIntoBookAndChaptersAndVerses(bible_reference_candidate, &book_candidate, &chapters_and_verses_candidate);
    return (chapters_and_verses_candidate.empty()) ? "4esra1-2" : "4esra" + chapters_and_verses_candidate;
}


std::string BibleAliasMapper::map(const std::string &bible_reference_candidate, const bool verbose) const {
    const std::string normalised_reference_candidate(StringUtil::Filter(TextUtil::UTF8ToLower(bible_reference_candidate), { ' ' }));
    if (StringUtil::StartsWith(normalised_reference_candidate, { "6esra", "6ezra", "6ezr", "6esr", "6esd" }, /* ignore_case */false))
        return Map6Esra(normalised_reference_candidate);
    if (StringUtil::StartsWith(normalised_reference_candidate, { "5esra", "5ezra", "5ezr", "5esr", "5esd" }, /* ignore_case */false))
        return Map5Esra(normalised_reference_candidate);

    const auto alias_and_canonical_form(aliases_to_canonical_forms_map_.find(normalised_reference_candidate));
    if (alias_and_canonical_form == aliases_to_canonical_forms_map_.end()) {
        if (verbose)
            std::cerr << "No mapping from \"" << bible_reference_candidate << "\" to a canonical form was found!\n";

        return bible_reference_candidate;
    }

    if (verbose)
        std::cerr << "Replaced " << bible_reference_candidate << " with " << alias_and_canonical_form->second << '\n';
    return alias_and_canonical_form->second;
}


} // namespace BibleUtil
