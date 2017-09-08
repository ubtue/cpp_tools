/** \brief A MARC-21 filter utility that can remove records or fields based on patterns for MARC subfields.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2016-2017 Universitätsbibliothek Tübingen.  All rights reserved.
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

#include <iostream>
#include <memory>
#include <unordered_set>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include "Compiler.h"
#include "DirectoryEntry.h"
#include "FileUtil.h"
#include "Leader.h"
#include "MarcRecord.h"
#include "MarcReader.h"
#include "MarcTag.h"
#include "MarcWriter.h"
#include "MarcXmlWriter.h"
#include "MediaTypeUtil.h"
#include "RegexMatcher.h"
#include "StringUtil.h"
#include "Subfields.h"
#include "TextUtil.h"
#include "util.h"


void Usage() {
    std::cerr << "usage: " << ::progname
              << "       marc_input marc_output [[--input-format=(marc-xml|marc-21)]\n"
              << "       [--output-format=(marc-xml|marc-21)] op1 [op2 .. opN]\n"
              << "       where each operation must start with the operation type. Operation-type flags\n"
              << "       are --drop, --keep, --drop-biblio-level, --keep-biblio-level --remove-fields,\n"
              << "       --remove-subfields, --filter-chars --max-count or --translate.  Arguments for --keep,\n"
              << "       --drop, and --remove-field are field_or_subfieldspec1:regex1\n"
              << "       [field_or_subfieldspec2:regex2 .. field_or_subfieldspecN:regexN] where\n"
              << "       \"field_or_subfieldspec\" must either be a MARC tag or a MARC tag followed by a\n"
              << "       single-character subfield code and \"regex\" is a Perl-compatible regular expression.\n"
              << "       Arguments for --remove-subfields are constructed accordingly but only subfield specs are\n"
              << "       permissible.  --drop-biblio-level and --keep-biblio-level arguments must one or more\n"
              << "       characters.  --filter-chars' arguments are\n"
              << "       subfield_spec1:subfield_spec2:...:subfield_specN characters_to_delete.\n"
              << "       --max-count has a single count numeric argument which specifies the maximum number of\n"
              << "       records to emit.\n"
              << "       The bibliographic-level operations are basically a comparsion against leader position 07.\n"
              << "       --translate is inspired by tr and is used to specify a mapping from one set of Unicode\n"
              << "       characters to another.  Arguments to --translate must be\n"
              << "       subfieldspec1[:subfieldspec2:..:subfieldspecN] set1 and set2 where both must\n"
              << "       be either explicit and equally long lists of individual characters or the sequences\n"
              << "       [:upper:] or [:lower:] where currently [:upper:] and [:lower:] may only be mapped to each\n"
              << "       other.\n"
              << "       If you don't specify an output format it will be the same as the input format.\n\n";

    std::exit(EXIT_FAILURE);
}


class CompiledPattern {
    std::string tag_;
    char subfield_code_;
    RegexMatcher matcher_;
public:
    static const char NO_SUBFIELD_CODE;
public:
    CompiledPattern(const std::string &tag, const char subfield_code,  const RegexMatcher &matcher)
        : tag_(tag), subfield_code_(subfield_code), matcher_(matcher) {}
    const std::string &getTag() const { return tag_; }
    bool hasSubfieldCode() const { return subfield_code_ != NO_SUBFIELD_CODE; }
    char getSubfieldCode() const { return subfield_code_; }
    bool fieldMatched(const std::string &field_contents) const;
    bool subfieldMatched(const std::string &subfield_contents) const;
};


const char CompiledPattern::NO_SUBFIELD_CODE('\0');


bool CompiledPattern::fieldMatched(const std::string &field_contents) const {
    std::string err_msg;
    const bool retval = matcher_.matched(field_contents, &err_msg);
    if (not retval and not err_msg.empty())
        Error("Unexpected error while trying to match a field in CompiledPattern::fieldMatched(): " + err_msg);

    return retval;
}


bool CompiledPattern::subfieldMatched(const std::string &subfield_contents) const {
    std::string err_msg;
    const bool retval = matcher_.matched(subfield_contents, &err_msg);
    if (not retval and not err_msg.empty())
        Error("Unexpected error while trying to match a subfield in CompiledPattern::subfieldMatched(): " + err_msg);

    return retval;
}


// Expects "patterns" to contain strings that look like TTTS:REGEX where TTT are 3 characters specifying a field,
// S is a subfield code and REGEX is a PCRE-style regex supporting UTF8 that should match subfield contents.
// Alteratively a pattern can look like TTT:REGEX where TTT is a tag and we have no subfield code.
bool CompilePatterns(const std::vector<std::string> &patterns,
                     std::vector<CompiledPattern *> * const compiled_patterns, std::string * const err_msg)
{
    compiled_patterns->clear();
    compiled_patterns->reserve(patterns.size());

    for (const auto &pattern : patterns) {
        std::string tag;
        char subfield_code;
        std::string::size_type first_colon_pos = pattern.find(':');
        if (first_colon_pos == std::string::npos) {
            *err_msg = "missing colon!";
            return false;
        } else if (first_colon_pos == DirectoryEntry::TAG_LENGTH) {
            tag = pattern.substr(0, 3);
            subfield_code = CompiledPattern::NO_SUBFIELD_CODE;
        } else if (first_colon_pos == DirectoryEntry::TAG_LENGTH + 1) {
            tag = pattern.substr(0, 3);
            subfield_code = pattern[3];
        } else {
            *err_msg = "colon in wrong position (" + std::to_string(first_colon_pos) + ")! (Tag length must be "
                       + std::to_string(DirectoryEntry::TAG_LENGTH) + ".)";
            return false;
        }

        const std::string regex_string(pattern.substr(first_colon_pos + 1));
        RegexMatcher * const new_matcher(RegexMatcher::RegexMatcherFactory(regex_string, err_msg));
        if (new_matcher == nullptr) {
            *err_msg = "failed to compile regular expression: \"" + regex_string + "\"! (" + *err_msg +")";
            return false;
        }

        compiled_patterns->push_back(new CompiledPattern(tag, subfield_code, std::move(*new_matcher)));
        delete new_matcher;
    }

    return true;
}


/** Returns true if we have at least one match. */
bool Matched(const MarcRecord &record, const std::vector<CompiledPattern *> &compiled_patterns,
             std::vector<size_t> * const matched_field_indices)
{
    matched_field_indices->clear();

    bool matched_at_least_one(false);
    for (const auto &compiled_pattern : compiled_patterns) {
        for (size_t index(record.getFieldIndex(compiled_pattern->getTag()));
             index < record.getNumberOfFields() and record.getTag(index) == compiled_pattern->getTag();
             ++index)
        {
            if (compiled_pattern->hasSubfieldCode()) {
                const Subfields subfields(record.getSubfields(index));
                const auto begin_end(subfields.getIterators(compiled_pattern->getSubfieldCode()));
                for (auto subfield_code_and_value(begin_end.first); subfield_code_and_value != begin_end.second;
                     ++subfield_code_and_value)
                {
                    if (compiled_pattern->subfieldMatched(subfield_code_and_value->value_)) {
                        matched_field_indices->emplace_back(index);
                        matched_at_least_one = true;
                    }
                }
            } else if (compiled_pattern->fieldMatched(record.getFieldData(index))) {
                matched_field_indices->emplace_back(index);
                matched_at_least_one = true;
            }
        }
    }

    return matched_at_least_one;
}


bool MatchedSubfield(const MarcRecord &record, const std::vector<CompiledPattern *> &compiled_patterns,
                     std::vector<std::pair<size_t,char>> * const matched_field_indices_and_subfields)
{
    matched_field_indices_and_subfields->clear();

    bool matched_at_least_one(false);
    for (const auto &compiled_pattern : compiled_patterns) {
        ssize_t index(record.getFieldIndex(compiled_pattern->getTag()));
        if (index == -1)
            continue;

        for (/* Intentionally empty! */;
             static_cast<size_t>(index) < record.getNumberOfFields()
             and record.getTag(index) == compiled_pattern->getTag(); ++index)
        {
            if (compiled_pattern->hasSubfieldCode()) {
                const Subfields subfields(record.getSubfields(index));
                const auto begin_end(subfields.getIterators(compiled_pattern->getSubfieldCode()));
                for (auto subfield_code_and_value(begin_end.first); subfield_code_and_value != begin_end.second;
                     ++subfield_code_and_value)
                {
                    if (compiled_pattern->subfieldMatched(subfield_code_and_value->value_)) {
                        matched_field_indices_and_subfields->emplace_back(index, subfield_code_and_value->code_);
                        matched_at_least_one = true;
                    }
                }
            }
        }
    }

    return matched_at_least_one;
}


namespace {


enum class OutputFormat { MARC_XML, MARC_21, SAME_AS_INPUT };
enum class FilterType { KEEP, DROP, KEEP_BIBLIOGRAPHIC_LEVEL, DROP_BIBLIOGRAPHIC_LEVEL, REMOVE_FIELDS,
                        REMOVE_SUBFIELDS, FILTER_CHARS, MAX_COUNT, TRANSLATE };


} // unnamed namespace


class TranslateMap {
public:
    virtual ~TranslateMap() { }

    virtual TranslateMap *clone() const = 0;

    /** \return True if "*s" was changed, else false. */
    virtual bool map(std::string * const s) const = 0;
};


class CharSetTranslateMap: public TranslateMap {
    std::wstring set1_, set2_;
public:
    CharSetTranslateMap(const std::string &set1, const std::string &set2);
    virtual bool map(std::string * const s) const final;
    virtual CharSetTranslateMap *clone() const final { return new CharSetTranslateMap(set1_, set2_); }
private:
    CharSetTranslateMap(const std::wstring &set1, const std::wstring &set2): set1_(set1), set2_(set2) { }
};


CharSetTranslateMap::CharSetTranslateMap(const std::string &set1, const std::string &set2) {
    if (unlikely(not TextUtil::UTF8toWCharString(set1, &set1_)))
        Error("in CharSetTranslateMap::CharSetTranslateMap: set1 \"" + set1 + "\" is not a valid UTF-8 string!");
    if (unlikely(not TextUtil::UTF8toWCharString(set2, &set2_)))
        Error("in CharSetTranslateMap::CharSetTranslateMap: set2 \"" + set2 + "\" is not a valid UTF-8 string!");
    if (set1_.size() != set2_.size())
        Error("in CharSetTranslateMap::CharSetTranslateMap: input sets must contain an equal number of Unicode "
              "characters!");
}


bool CharSetTranslateMap::map(std::string * const s) const {
    std::wstring ws;
    if (unlikely(not TextUtil::UTF8toWCharString(*s, &ws)))
        Error("in CharSetTranslateMap::map: input \"" + *s + "\" is not a valid UTF-8 string!");

    bool changed(false);
    for (auto wch(ws.begin()); wch != ws.end(); ++wch) {
        const auto pos(set1_.find(*wch));
        if (pos != std::wstring::npos) {
            *wch = set2_[pos];
            changed = true;
        }
    }

    if (unlikely(not TextUtil::WCharToUTF8String(ws, s)))
        Error("in CharSetTranslateMap::map: TextUtil::WCharToUTF8String() failed! (This should *never* happen!)");

    return changed;
}


class UpperLowerTranslateMap: public TranslateMap {
public:
    enum MapType { UPPER_TO_LOWER, LOWER_TO_UPPER };
private:
    MapType map_type_;
public:
    UpperLowerTranslateMap(const MapType map_type): map_type_(map_type) { }
    virtual bool map(std::string * const s) const final;
    virtual UpperLowerTranslateMap *clone() const final { return new UpperLowerTranslateMap(map_type_); }
};


bool UpperLowerTranslateMap::map(std::string * const s) const {
    std::wstring ws;
    if (unlikely(not TextUtil::UTF8toWCharString(*s, &ws)))
        Error("in UpperLowerTranslateMap::map: input \"" + *s + "\" is not a valid UTF-8 string!");

    bool changed(false);
    if (map_type_ == UPPER_TO_LOWER) {
        for (auto wch(ws.begin()); wch != ws.end(); ++wch) {
            if (std::iswupper(static_cast<wint_t>(*wch))) {
                *wch = std::towlower(*wch);
                changed = true;
            }
        }
    } else { // map_type_ == LOWER_TO_UPPER.
        for (auto wch(ws.begin()); wch != ws.end(); ++wch) {
            if (std::iswlower(static_cast<wint_t>(*wch))) {
                *wch = std::towupper(*wch);
                changed = true;
            }
        }
    }

    if (unlikely(not TextUtil::WCharToUTF8String(ws, s)))
        Error("in UpperLowerTranslateMap::map: TextUtil::WCharToUTF8String() failed! (This should *never* happen!)");

    return changed;
}


class FilterDescriptor {
private:
    FilterType filter_type_;
    std::vector<CompiledPattern *> compiled_patterns_;
    std::vector<std::string> subfield_specs_;
    std::string chars_to_delete_;
    std::string biblio_levels_;
    mutable unsigned count_;
    unsigned max_count_;
    TranslateMap *translate_map_;
public:
    inline FilterType getFilterType() const { return filter_type_; }
    inline const std::string &getBiblioLevels() const { return biblio_levels_; }
    bool skipRecordDueToExceededRecordCount() const { ++count_; return count_ > max_count_; }

    /** \note Only call this if the filter type is not FILTER_CHARS! */
    inline const std::vector<CompiledPattern *> getCompiledPatterns() const { return compiled_patterns_; }

    /** \note Only call this if the filter type is FILTER_CHARS! */
    inline const std::vector<std::string> &getSubfieldSpecs() const { return subfield_specs_; }

    /** \note Only call this if the filter type is FILTER_CHARS! */
    inline const std::string &getCharsToDelete() const { return chars_to_delete_; }

    /** \note Only call this if the filter type is TRANSLATE! */
    inline const TranslateMap &getTranslateMap() const { return *translate_map_; }

    inline static FilterDescriptor MakeDropFilter(const std::vector<CompiledPattern *> &compiled_patterns) {
        return FilterDescriptor(FilterType::DROP, compiled_patterns);
    }

    inline static FilterDescriptor MakeKeepFilter(const std::vector<CompiledPattern *> &compiled_patterns) {
        return FilterDescriptor(FilterType::KEEP, compiled_patterns);
    }

    inline static FilterDescriptor MakeDropBiblioLevelFilter(const std::string &biblio_levels) {
        return FilterDescriptor(FilterType::DROP_BIBLIOGRAPHIC_LEVEL, biblio_levels);
    }

    inline static FilterDescriptor MakeKeepBiblioLevelFilter(const std::string &biblio_levels) {
        return FilterDescriptor(FilterType::KEEP_BIBLIOGRAPHIC_LEVEL, biblio_levels);
    }

    inline static FilterDescriptor MakeRemoveFieldsFilter(const std::vector<CompiledPattern *> &compiled_patterns) {
        return FilterDescriptor(FilterType::REMOVE_FIELDS, compiled_patterns);
    }

    inline static FilterDescriptor MakeRemoveSubfieldsFilter(const std::vector<CompiledPattern *> &compiled_patterns)
    {
        return FilterDescriptor(FilterType::REMOVE_SUBFIELDS, compiled_patterns);
    }

    inline static FilterDescriptor MakeFilterCharsFilter(const std::vector<std::string> &subfield_specs,
                                                         const std::string &chars_to_delete)
    {
        return FilterDescriptor(subfield_specs, chars_to_delete);
    }

    inline static FilterDescriptor MakeMaxCountFilter(const unsigned max_count) {
        return FilterDescriptor(max_count);
    }

    inline static FilterDescriptor MakeTranslateFilter(const std::vector<std::string> &subfield_specs,
                                                       const TranslateMap &translate_map)
    {
        return FilterDescriptor(subfield_specs, translate_map);
    }
private:
    FilterDescriptor(const FilterType filter_type, const std::vector<CompiledPattern *> &compiled_patterns)
        : filter_type_(filter_type), compiled_patterns_(compiled_patterns), translate_map_(nullptr) { }
    FilterDescriptor(const std::vector<std::string> &subfield_specs, const std::string &chars_to_delete)
        : filter_type_(FilterType::FILTER_CHARS), subfield_specs_(subfield_specs),
          chars_to_delete_(chars_to_delete), translate_map_(nullptr) { }
    FilterDescriptor(const FilterType filter_type, const std::string &biblio_levels)
        : filter_type_(filter_type), biblio_levels_(biblio_levels) { }
    FilterDescriptor(const unsigned max_count)
        : filter_type_(FilterType::MAX_COUNT), count_(0), max_count_(max_count), translate_map_(nullptr) { }
    FilterDescriptor(const std::vector<std::string> &subfield_specs, const TranslateMap &translate_map)
        : filter_type_(FilterType::TRANSLATE), subfield_specs_(subfield_specs),
          translate_map_(translate_map.clone()) { }
};


std::string GetSubfieldCodes(const MarcTag &tag, const std::vector<std::string> &subfield_specs) {
    std::string subfield_codes;

    for (const auto &subfield_spec : subfield_specs) {
        if (tag == subfield_spec.substr(0, DirectoryEntry::TAG_LENGTH))
            subfield_codes += subfield_spec[DirectoryEntry::TAG_LENGTH];
    }

    return subfield_codes;
}


/** \brief Removes any of the characters in "chars_to_delete" from all of the subfields specified by "subfield_specs".
 *  \return True if at least one subfield has been modified, else false.
 */
bool FilterCharacters(const std::vector<std::string> &subfield_specs, const std::string &chars_to_delete,
                      MarcRecord * const record)
{
    bool modified_at_least_one_field(false);
    for (size_t field_index(0); field_index < record->getNumberOfFields(); ++field_index) {
        const std::string subfield_codes(GetSubfieldCodes(record->getTag(field_index), subfield_specs));
        if (subfield_codes.empty())
            continue;

        bool modified_at_least_one_subfield(false);
        Subfields subfields(record->getSubfields(field_index));
        for (const auto subfield_code : subfield_codes) {
            const auto begin_end(subfields.getIterators(subfield_code));
            for (auto subfield(begin_end.first); subfield != begin_end.second; ++subfield) {
                const auto old_length(subfield->value_.length());
                StringUtil::RemoveChars(chars_to_delete, &(subfield->value_));
                if (subfield->value_.length() != old_length)
                    modified_at_least_one_subfield = true;
            }
        }

        if (modified_at_least_one_subfield) {
            modified_at_least_one_field = true;
            record->updateField(field_index, subfields.toString());
        }
    }

    return modified_at_least_one_field;
}


/** \brief Maps contents of the subfields specified by "subfield_specs".
 *  \return True if at least one subfield has been modified, else false.
 */
bool TranslateCharacters(const std::vector<std::string> &subfield_specs, const TranslateMap &translate_map,
                         MarcRecord * const record)
{
    bool modified_at_least_one_field(false);
    for (size_t field_index(0); field_index < record->getNumberOfFields(); ++field_index) {
        const std::string subfield_codes(GetSubfieldCodes(record->getTag(field_index), subfield_specs));
        if (subfield_codes.empty())
            continue;

        bool modified_at_least_one_subfield(false);
        Subfields subfields(record->getSubfields(field_index));
        for (const auto subfield_code : subfield_codes) {
            const auto begin_end(subfields.getIterators(subfield_code));
            for (auto subfield(begin_end.first); subfield != begin_end.second; ++subfield) {
                if (translate_map.map(&(subfield->value_)))
                    modified_at_least_one_subfield = true;
            }
        }

        if (modified_at_least_one_subfield) {
            modified_at_least_one_field = true;
            record->updateField(field_index, subfields.toString());
        }
    }

    return modified_at_least_one_field;
}


void Filter(const std::vector<FilterDescriptor> &filters, MarcReader * const marc_reader,
            MarcWriter * const marc_writer)
{
    unsigned total_count(0), deleted_count(0), modified_count(0);
    while (MarcRecord record = marc_reader->read()) {
        ++total_count;
        bool deleted_record(false), modified_record(false);
        for (const auto &filter : filters) {
            if (filter.getFilterType() == FilterType::MAX_COUNT) {
                if (filter.skipRecordDueToExceededRecordCount()) {
                    --total_count;
                    goto print_counts;
                }
            } else if (filter.getFilterType() == FilterType::FILTER_CHARS) {
                if (FilterCharacters(filter.getSubfieldSpecs(), filter.getCharsToDelete(), &record))
                    modified_record = true;
            } else if (filter.getFilterType() == FilterType::DROP_BIBLIOGRAPHIC_LEVEL) {
                if (std::strchr(filter.getBiblioLevels().c_str(), record.getLeader().getBibliographicLevel())
                    != nullptr)
                {
                    deleted_record = true;
                    break;
                }
            } else if (filter.getFilterType() == FilterType::KEEP_BIBLIOGRAPHIC_LEVEL) {
                if (std::strchr(filter.getBiblioLevels().c_str(), record.getLeader().getBibliographicLevel())
                                != nullptr)
                {
                    deleted_record = true;
                    break;
                }
            } else if (filter.getFilterType() == FilterType::REMOVE_SUBFIELDS) {
               std::vector<std::pair<size_t, char>> matched_field_indices_and_subfields;
               if (MatchedSubfield(record, filter.getCompiledPatterns(), &matched_field_indices_and_subfields)) {
                   std::sort(matched_field_indices_and_subfields.begin(), matched_field_indices_and_subfields.end());
                   for (const auto field_index_and_subfield : matched_field_indices_and_subfields)
                        record.deleteSubfield(field_index_and_subfield.first, field_index_and_subfield.second);
                   modified_record = true;
                   break;
               }
            } else if (filter.getFilterType() == FilterType::TRANSLATE) {
                if (TranslateCharacters(filter.getSubfieldSpecs(), filter.getTranslateMap(), &record))
                    modified_record = true;
            } else {
                std::vector<size_t> matched_field_indices;
                if (Matched(record, filter.getCompiledPatterns(), &matched_field_indices)) {
                    if (filter.getFilterType() == FilterType::DROP) {
                        deleted_record = true;
                        break;
                    } else if (filter.getFilterType() == FilterType::REMOVE_FIELDS) {
                        std::sort(matched_field_indices.begin(), matched_field_indices.end(), std::greater<size_t>());
                        for (const auto field_index : matched_field_indices)
                            record.deleteField(field_index);
                        modified_record = true;
                    }
                } else if (filter.getFilterType() == FilterType::KEEP) {
                    deleted_record = true;
                    break;
                }
            }
        }

        if (deleted_record)
            ++deleted_count;
        else {
            if (modified_record)
                ++modified_count;
            marc_writer->write(record);
        }
    }

print_counts:
    std::cerr << "Processed a total of " << total_count << " record(s).\n";
    std::cerr << "Kept " << (total_count - deleted_count) << " record(s).\n";
    std::cerr << "Modified " << modified_count << " record(s).\n";
    std::cerr << "Deleted " << deleted_count << " record(s).\n";
}


std::vector<CompiledPattern *> CollectAndCompilePatterns(char ***argvp) {
    const std::string operation_type(**argvp);
    ++*argvp;

    std::vector<std::string> specs_and_pattern;
    while (**argvp != nullptr and not StringUtil::StartsWith(**argvp, "--")) {
        specs_and_pattern.emplace_back(**argvp);
        ++*argvp;
    }

    if (specs_and_pattern.empty())
        Error("expected at least one field or subfield specification after \"" + operation_type + "\"!");

    std::vector<CompiledPattern *> compiled_patterns;
    std::string err_msg;
    if (not CompilePatterns(specs_and_pattern, &compiled_patterns, &err_msg))
        Error("bad field specification and or regular expression (" + err_msg + ")!");

    return compiled_patterns;
}


// Sanity check.
bool ArePlausibleSubfieldSpecs(const std::vector<std::string> &subfield_specs) {
    if (subfield_specs.empty())
        return false;

    for (const auto &subfield_spec : subfield_specs) {
        if (subfield_spec.length() != (DirectoryEntry::TAG_LENGTH + 1))
            return false;
    }

    return true;
}


std::string GetBiblioLevelArgument(char ***argvp) {
    ++*argvp;
    if (*argvp == nullptr)
        Error("missing bibliographic level after --drop-biblio-level or --keep-biblio-level flag!");
    const std::string bibliographic_level_candidate(**argvp);
    ++*argvp;

    if (bibliographic_level_candidate.empty())
        Error("bad empty bibliographic level!");
    return bibliographic_level_candidate;
}


unsigned TestAndConvertCount(char ***argvp) {
    ++*argvp;
    if (*argvp == nullptr)
        Error("missing count value after --max-count flag!");

    unsigned max_count;
    if (not StringUtil::ToUnsigned(**argvp, &max_count))
        Error("\"" + std::string(**argvp) + "\" is not a valid count argument for the --max-count flag!");
    ++*argvp;

    return max_count;
}


void ExtractSubfieldSpecs(const std::string &command, char **argv, std::vector<std::string> * const subfield_specs) {
    ++argv;
    StringUtil::Split(*argv, ':', subfield_specs);
    if (not ArePlausibleSubfieldSpecs(*subfield_specs))
        Error("bad subfield specifications \"" + std::string(*argv) + "\" for " + command + "!");
    ++argv;
}


void ProcessFilterArgs(char **argv, std::vector<FilterDescriptor> * const filters) {
    while (*argv != nullptr) {
        std::vector<CompiledPattern *> compiled_patterns;
        if (std::strcmp(*argv, "--max-count") == 0)
            filters->emplace_back(FilterDescriptor::MakeMaxCountFilter(TestAndConvertCount(&argv)));
        else if (std::strcmp(*argv, "--drop") == 0)
            filters->emplace_back(FilterDescriptor::MakeDropFilter(CollectAndCompilePatterns(&argv)));
        else if (std::strcmp(*argv, "--keep") == 0)
            filters->emplace_back(FilterDescriptor::MakeKeepFilter(CollectAndCompilePatterns(&argv)));
        else if (std::strcmp(*argv, "--drop-biblio-level") == 0)
            filters->emplace_back(FilterDescriptor::MakeDropBiblioLevelFilter(GetBiblioLevelArgument(&argv)));
        else if (std::strcmp(*argv, "--keep-biblio-level") == 0)
            filters->emplace_back(FilterDescriptor::MakeKeepBiblioLevelFilter(GetBiblioLevelArgument(&argv)));
        else if (std::strcmp(*argv, "--remove-fields") == 0)
            filters->emplace_back(FilterDescriptor::MakeRemoveFieldsFilter(CollectAndCompilePatterns(&argv)));
        else if (std::strcmp(*argv, "--remove-subfields") == 0)
            filters->emplace_back(FilterDescriptor::MakeRemoveSubfieldsFilter(CollectAndCompilePatterns(&argv)));
        else if (std::strcmp(*argv, "--translate") == 0) {
            std::vector<std::string> subfield_specs;
            ExtractSubfieldSpecs("--translate", argv, &subfield_specs);
            if (argv == nullptr or StringUtil::StartsWith(*argv, "--"))
                Error("missing or bad \"set1\" argument to \"--translate\"!");
            if (argv + 1 == nullptr or StringUtil::StartsWith(*(argv + 1), "--"))
                Error("missing or bad \"set2\" argument to \"--translate\"!");
            TranslateMap *translate_map;
            if (std::strcmp(*argv, "[:upper:]") == 0 or std::strcmp(*argv, "[:lower:]") == 0) {
                if (std::strcmp(*argv, "[:upper:]") == 0) {
                    if (std::strcmp(*(argv + 1), "[:lower:]") != 0)
                        Error("if \"[:upper:]\" was specified as set1 for --translate, \"[:lower:]\" must be "
                              "specified as set2!");
                    translate_map = new UpperLowerTranslateMap(UpperLowerTranslateMap::UPPER_TO_LOWER);
                } else {
                   if (std::strcmp(*(argv + 1), "[:upper:]") != 0)
                        Error("if \"[:lower:]\" was specified as set1 for --translate, \"[:upper:]\" must be "
                              "specified as set2!");
                    translate_map = new UpperLowerTranslateMap(UpperLowerTranslateMap::LOWER_TO_UPPER);
                 }
            } else
                translate_map = new CharSetTranslateMap(*argv, *(argv + 1));
            filters->emplace_back(FilterDescriptor::MakeTranslateFilter(subfield_specs, *translate_map));
            argv += 2;
        } else if (std::strcmp(*argv, "--filter-chars") == 0) {
            std::vector<std::string> subfield_specs;
            ExtractSubfieldSpecs("--filter-chars", argv, &subfield_specs);
            if (argv == nullptr or StringUtil::StartsWith(*argv, "--"))
                Error("missing or bad \"characters_to_delete\" argument to \"--filter-chars\"!");
            filters->emplace_back(FilterDescriptor::MakeFilterCharsFilter(subfield_specs, *argv++));
        } else
            Error("unknown operation type \"" + std::string(*argv) + "\"!");
    }
}


int main(int argc, char **argv) {
    ::progname = argv[0];
    ++argv;

    if (argc < 5)
        Usage();

    const std::string input_filename(*argv++);
    const std::string output_filename(*argv++);

    MarcReader::ReaderType reader_type(MarcReader::AUTO);
    if (std::strcmp("--input-format=marc-xml", *argv) == 0) {
        reader_type = MarcReader::XML;
        ++argv;
    } else if (std::strcmp("--input-format=marc-21", *argv) == 0) {
        reader_type = MarcReader::BINARY;
        ++argv;
    }
    std::unique_ptr<MarcReader> marc_reader(MarcReader::Factory(input_filename, reader_type));

    MarcWriter::WriterType writer_type;
    if (std::strcmp("--output-format=marc-xml", *argv) == 0) {
        writer_type = MarcWriter::XML;
        ++argv;
    } else if (std::strcmp("--output-format=marc-21", *argv) == 0) {
        writer_type = MarcWriter::BINARY;
        ++argv;
    } else
        writer_type = (marc_reader->getReaderType() == MarcReader::BINARY) ? MarcWriter::BINARY : MarcWriter::XML;
    std::unique_ptr<MarcWriter> marc_writer(MarcWriter::Factory(output_filename, writer_type));

    try {
        std::vector<FilterDescriptor> filters;
        ProcessFilterArgs(argv, &filters);

        Filter(filters, marc_reader.get(), marc_writer.get());
    } catch (const std::exception &x) {
        Error("caught exception: " + std::string(x.what()));
    }
}
