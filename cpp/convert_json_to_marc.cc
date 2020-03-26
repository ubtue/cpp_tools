/** \file    convert_json_to_marc.cc
 *  \brief   Converts JSON to MARC.
 *  \author  Dr. Johannes Ruscheinski
 */

/*
    Copyright (C) 2020 Library of the University of Tübingen

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Affero General Public License as
    published by the Free Software Foundation, either version 3 of the
    License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Affero General Public License for more details.

    You should have received a copy of the GNU Affero General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <algorithm>
#include <iostream>
#include <limits>
#include <unordered_map>
#include <utility>
#include <vector>
#include "FileUtil.h"
#include "IniFile.h"
#include "JSON.h"
#include "KeyValueDB.h"
#include "MARC.h"
#include "MiscUtil.h"
#include "RegexMatcher.h"
#include "TimeUtil.h"
#include "UBTools.h"
#include "util.h"


namespace {


[[noreturn]] void Usage() {
    ::Usage("[--create-unique-id-db|--ignore-unique-id-dups|--extract-and-count-issns-only] config_file json_input [marc_output]\n"
            "\t--create-unique-id-db: This flag has to be specified the first time this program will be executed only.\n"
            "\t--ignore-unique-id-dups: If specified MARC records will be created for unique ID's which we have encountered\n"
            "\t                         before.  The unique ID database will still be updated.\n"
            "\t--extract-and-count-issns-only: Generates stats on the frequency of ISSN's in the JSON input and does not generate any \n"
            "\t                                MARC output files.  This requires the existence of the \"magic\" \"ISSN\" config file entry!\n"
            "\tmarc_outpt: required unless --extract-and-count-issns-only was specified!\n\n");
}


struct JournalTitleAndPPN {
    std::string journal_title_;
    std::string ppn_;
public:
    JournalTitleAndPPN(const std::string &journal_title, const std::string &ppn)
        : journal_title_(journal_title), ppn_(ppn) { }
};


std::vector<std::string> SplitLineOnColons(const std::string &line) {
    std::vector<std::string> parts;

    bool escaped(false);
    parts.push_back("");
    for (const char ch : line) {
        if (escaped) {
            parts.back() += ch;
            escaped = false;
        } else if (ch == '\\')
            escaped = true;
        else if (ch == ':')
            parts.push_back("");
        else
            parts.back() += ch;
    }
    if (escaped)
        parts.clear(); // This way we signal to the caller that we have a bad input line.

    return parts;
}


// Parses an input file that has three (the last component may be empty) parts per line that are colon-separated.  Embedded colons may
// be backslash escaped.
void LoadISSNsToJournalTitlesAndPPNsMap(std::unordered_map<std::string, JournalTitleAndPPN> * const issns_to_journal_titles_and_ppns_map) {
    const std::string MAP_FILE_PATH(UBTools::GetTuelibPath() + "issns_to_journaltitles_and_ppns.map");
    const auto input(FileUtil::OpenInputFileOrDie(MAP_FILE_PATH));

    unsigned line_no(0);
    while (not input->eof()) {
        ++line_no;
        const std::string line(input->getline());
        if (line.empty())
            continue;
        const std::vector<std::string> parts(SplitLineOnColons(line));
        if (parts.size() != 3 or parts[0].empty() or parts[1].empty()) // ISSN and titles are required, PPN's are optionsl.
            LOG_ERROR("malformed line #" + std::to_string(line_no) + " in \"" + MAP_FILE_PATH + "\"!");
        issns_to_journal_titles_and_ppns_map->emplace(parts[0], JournalTitleAndPPN(parts[1], parts[2]));
    }
}


struct FieldDescriptor {
    std::string name_;
    std::string tag_, overflow_tag_;
    char indicator1_, indicator2_;
    bool repeat_field_;
    std::vector<std::pair<char, std::string>> subfield_codes_to_json_tags_, subfield_codes_to_prefixes_,
        subfield_codes_to_fixed_subfields_; // For mapping to variable fields
    std::map<char, std::shared_ptr<RegexMatcher>> subfield_codes_to_extraction_regexes_map_;
    std::string json_tag_; // For mapping to control fields
    std::string field_contents_prefix_; // For mapping to control fields
    bool map_to_marc_language_code_;
    bool normalise_issn_;
    bool required_;
public:
    explicit FieldDescriptor(const std::string &name, const std::string &tag, const std::string &overflow_tag, const char indicator1,
                             const char indicator2, const bool repeat_field,
                             const std::vector<std::pair<char, std::string>> &subfield_codes_to_json_tags,
                             const std::vector<std::pair<char, std::string>> &subfield_codes_to_prefixes,
                             const std::vector<std::pair<char, std::string>> &subfield_codes_to_fixed_subfields,
                             const std::map<char, std::shared_ptr<RegexMatcher>> subfield_codes_to_extraction_regexes_map,
                             const std::string &json_tag, const std::string &field_contents_prefix, const bool map_to_marc_language_code,
                             const bool normalise_issn, const bool required);
    bool operator<(const FieldDescriptor &other) const { return tag_ < other.tag_; }
};


FieldDescriptor::FieldDescriptor(const std::string &name, const std::string &tag, const std::string &overflow_tag, const char indicator1,
                                 const char indicator2, const bool repeat_field,
                                 const std::vector<std::pair<char, std::string>> &subfield_codes_to_json_tags,
                                 const std::vector<std::pair<char, std::string>> &subfield_codes_to_prefixes,
                                 const std::vector<std::pair<char, std::string>> &subfield_codes_to_fixed_subfields,
                                 const std::map<char, std::shared_ptr<RegexMatcher>> subfield_codes_to_extraction_regexes_map,
                                 const std::string &json_tag, const std::string &field_contents_prefix,
                                 const bool map_to_marc_language_code, const bool normalise_issn, const bool required)
    : name_(name), tag_(tag), overflow_tag_(overflow_tag), indicator1_(indicator1), indicator2_(indicator2), repeat_field_(repeat_field),
      subfield_codes_to_json_tags_(subfield_codes_to_json_tags), subfield_codes_to_prefixes_(subfield_codes_to_prefixes),
      subfield_codes_to_fixed_subfields_(subfield_codes_to_fixed_subfields),
      subfield_codes_to_extraction_regexes_map_(subfield_codes_to_extraction_regexes_map), json_tag_(json_tag),
      field_contents_prefix_(field_contents_prefix), map_to_marc_language_code_(map_to_marc_language_code),
      normalise_issn_(normalise_issn), required_(required)
{
    if (not overflow_tag_.empty() and repeat_field_)
        LOG_ERROR("field \"" + name_ + "\" can't have both, an over flow tag and being a repeat field!");

    if (subfield_codes_to_json_tags_.empty() and json_tag_.empty())
        LOG_ERROR("field \"" + name_
                  + "\" is missing a mapping to the contents of a control field or to the contents of data subfields!");
}


class JSONNodeToBibliographicLevelMapper {
    std::string json_tag_;
    MARC::Record::BibliographicLevel default_;
    std::vector<std::pair<RegexMatcher *, MARC::Record::BibliographicLevel>> regex_to_bibliographic_level_map;
public:
    JSONNodeToBibliographicLevelMapper(const std::string &item_type_tag, const std::string &item_type_map);
    ~JSONNodeToBibliographicLevelMapper();
    MARC::Record::BibliographicLevel getBibliographicLevel(const JSON::ObjectNode &object_node) const;
    MARC::Record::BibliographicLevel getBibliographicLevel(const std::string &string_value) const;
};


MARC::Record::BibliographicLevel MapTypeStringToBibliographicLevel(const std::string &item_type) {
    if (item_type == "monograph")
        return MARC::Record::MONOGRAPH_OR_ITEM;
    else if (item_type == "book chapter")
        return MARC::Record::MONOGRAPHIC_COMPONENT_PART;
    else if (item_type == "journal article")
        return MARC::Record::SERIAL_COMPONENT_PART;
    else
        LOG_ERROR("\"" + item_type + "\" is not a valid item type!");
}


bool SplitPatternsAndTypes(const std::string &patterns_and_types, std::vector<std::pair<std::string, std::string>> * const split_pairs) {
    bool escaped(false), in_pattern(true);
    std::string pattern, type;
    for (const char ch : patterns_and_types) {
        if (escaped) {
            escaped = false;
            if (in_pattern)
                pattern += ch;
            else
                type += ch;
        } else if (ch == '\\')
            escaped = true;
        else if (ch == '|') {
            split_pairs->emplace_back(pattern, type);
            pattern.clear(), type.clear();
            in_pattern = true;
        } else if (ch == ':') {
            if (not in_pattern) // types may not contain colons!
                return false;
            in_pattern = false;
        } else if (in_pattern)
            pattern += ch;
        else
            type += ch;
    }

    if (not escaped and not in_pattern) {
        split_pairs->emplace_back(pattern, type);
        return true;
    }

    return false;
}


JSONNodeToBibliographicLevelMapper::JSONNodeToBibliographicLevelMapper(const std::string &item_type_tag, const std::string &item_type_map)
    : json_tag_(item_type_tag)
{
    default_ = MARC::Record::UNDEFINED;

    std::vector<std::pair<std::string, std::string>> patterns_and_types;
    if (not SplitPatternsAndTypes(item_type_map, &patterns_and_types))
        LOG_ERROR("bad structure of value to item_type_map in Global section!");
    for (auto pattern_and_type(patterns_and_types.cbegin()); pattern_and_type != patterns_and_types.cend(); ++pattern_and_type) {
        if (pattern_and_type->first.empty()) {
            if (pattern_and_type != patterns_and_types.cend() - 1)
                LOG_ERROR("default w/o pattern must be the last entry in the pattern to item type mapping!");
            default_ = MapTypeStringToBibliographicLevel(pattern_and_type->second);
            return;
        }

        std::string err_msg;
        const auto regex(RegexMatcher::RegexMatcherFactory(pattern_and_type->first, &err_msg, RegexMatcher::ENABLE_UTF8 | RegexMatcher::CASE_INSENSITIVE));
        if (regex == nullptr)
            LOG_ERROR("bad regex pattern in pattern to item type mapping: \"" + pattern_and_type->first + "\"! (" + err_msg + ")");

        regex_to_bibliographic_level_map.emplace_back(regex, MapTypeStringToBibliographicLevel(pattern_and_type->second));
    }
}


JSONNodeToBibliographicLevelMapper::~JSONNodeToBibliographicLevelMapper() {
    for (const auto &regex_and_bibliographic_level : regex_to_bibliographic_level_map)
        delete regex_and_bibliographic_level.first;
}


MARC::Record::BibliographicLevel JSONNodeToBibliographicLevelMapper::getBibliographicLevel(const std::string &string_value) const {
    for (const auto &regex_and_bibliographic_level : regex_to_bibliographic_level_map) {
        if (regex_and_bibliographic_level.first->matched(string_value))
            return regex_and_bibliographic_level.second;
    }

    return default_;
}


MARC::Record::BibliographicLevel JSONNodeToBibliographicLevelMapper::getBibliographicLevel(const JSON::ObjectNode &object_node) const {
    if (json_tag_.empty())
        return default_;

    const auto string_or_array_node(object_node.getNode(json_tag_));
    if (string_or_array_node == nullptr)
        return default_;

    const auto node_type(string_or_array_node->getType());
    if (node_type == JSON::JSONNode::STRING_NODE)
        return getBibliographicLevel(JSON::JSONNode::CastToStringNodeOrDie("string_or_array_node", string_or_array_node)->getValue());

    if (node_type != JSON::JSONNode::ARRAY_NODE)
        LOG_ERROR("item type node \"" + json_tag_ + "\" is neither a string nor an array node but a "
                  + JSON::JSONNode::TypeToString(node_type) + "!");

    const auto array_node(JSON::JSONNode::CastToArrayNodeOrDie("string_or_array_node", string_or_array_node));
    for (const auto element_node : *array_node) {
        const auto bibliographic_level(getBibliographicLevel(JSON::JSONNode::CastToStringNodeOrDie("element_node", element_node)->getValue()));
        if (bibliographic_level != default_)
            return bibliographic_level;
    }

    return default_;
}


void ProcessGlobalSection(const IniFile::Section &global_section, std::string * const root_path,
                          std::unique_ptr<JSONNodeToBibliographicLevelMapper> * const json_node_to_bibliographic_level_mapper)
{
    *root_path = global_section.getString("root_path");

    if (global_section.hasEntry("item_type_tag") and not global_section.hasEntry("item_type_map"))
        LOG_ERROR("Global section \"has item_type_tag\" but not \"item_type_map\"!");

    if (not global_section.hasEntry("item_type_tag") and global_section.hasEntry("item_type_map"))
        LOG_ERROR("Global section \"has item_type_map\" but not \"item_type_tag\"!");

    std::string item_type_tag, item_type_map;
    if (global_section.hasEntry("item_type_tag")) {
        item_type_tag = global_section.getString("item_type_tag");
        item_type_map = global_section.getString("item_type_map");
    }

    json_node_to_bibliographic_level_mapper->reset(new JSONNodeToBibliographicLevelMapper(item_type_tag, item_type_map));
}


std::vector<FieldDescriptor> LoadFieldDescriptors(const std::string &inifile_path, std::string * const root_path,
                                                  std::unique_ptr<JSONNodeToBibliographicLevelMapper> * const json_node_to_bibliographic_level_mapper)
{
    std::vector<FieldDescriptor> field_descriptors;

    const IniFile ini_file(inifile_path);
    for (const auto &section : ini_file) {
        const auto &section_name(section.getSectionName());
        if (section_name.empty())
            continue;

        if (section_name == "Global")
            ProcessGlobalSection(section, root_path, json_node_to_bibliographic_level_mapper);
        else { // A section describing a mapping to a field
            const auto tag(section.getString("tag", ""));
            if (tag.empty())
                LOG_ERROR("missing tag in section \"" + section_name + "\" in \"" + ini_file.getFilename() + "\"!");
            if (tag.length() != MARC::Record::TAG_LENGTH)
                LOG_ERROR("invalid tag \"" + tag + "\" in section \"" + section_name + "\" in \"" + ini_file.getFilename() + "\"!");

            std::vector<std::pair<char, std::string>> subfield_codes_to_json_tags, subfield_codes_to_prefixes, subfield_codes_to_fixed_subfields;
            std::map<char, std::shared_ptr<RegexMatcher>> subfield_codes_to_extraction_regexes_map;
            for (const auto section_entry : section) {
                if (StringUtil::StartsWith(section_entry.name_, "add_fixed_subfield_")) {
                    if (section_entry.name_.length() != __builtin_strlen("add_fixed_subfield_?")) // Note: ? used as a placeholder for a subfield code
                        LOG_ERROR("invalid section entry in section \"" + section_name + "\": \"" + section_entry.name_ + "\"!");
                    const char subfield_code(section_entry.name_.back());
                    const auto fixed_subfield_value(section_entry.value_);
                    subfield_codes_to_fixed_subfields.emplace_back(subfield_code, fixed_subfield_value);
                    continue;
                }

                if (not StringUtil::StartsWith(section_entry.name_, "subfield_"))
                    continue;

                if (StringUtil::EndsWith(section_entry.name_, "_prefix")) {
                    if (section_entry.name_.length() != __builtin_strlen("subfield_?_prefix")) // Note: ? used as a placeholder for a subfield code
                        LOG_ERROR("invalid section entry in section \"" + section_name + "\": \"" + section_entry.name_ + "\"!");
                    const char subfield_code(section_entry.name_[__builtin_strlen("subfield_")]);
                    const auto subfield_prefix(section_entry.value_);
                    subfield_codes_to_prefixes.emplace_back(subfield_code, subfield_prefix);
                    continue;
                }

                if (StringUtil::EndsWith(section_entry.name_, "_extraction_regex")) {
                    if (section_entry.name_.length() != __builtin_strlen("subfield_?_extraction_regex")) // Note: ? used as a placeholder for a subfield code
                        LOG_ERROR("invalid section entry in section \"" + section_name + "\": \"" + section_entry.name_ + "\"!");
                    const char subfield_code(section_entry.name_[__builtin_strlen("subfield_")]);
                    const auto extraction_regex(section_entry.value_);
                    std::string error_message;
                    const auto regex_matcher(RegexMatcher::RegexMatcherFactory(extraction_regex, &error_message));
                    if (regex_matcher == nullptr)
                        LOG_ERROR("bad regex for \"" + section_entry.name_ + "\" in section \"" + section_name + "\"! ("
                                  + error_message + ")");
                    subfield_codes_to_extraction_regexes_map.emplace(subfield_code, regex_matcher);
                    continue;
                }

                if (section_entry.name_.length() != __builtin_strlen("subfield_?")) // Note: ? used as a placeholder for a subfield code
                    LOG_ERROR("invalid section entry in section \"" + section_name + "\": \"" + section_entry.name_ + "\"!");
                const char subfield_code(section_entry.name_.back());
                const auto json_tag(section_entry.value_);
                subfield_codes_to_json_tags.emplace_back(subfield_code, json_tag);
            }
            const auto json_tag(section.getString("json_tag", ""));
            if (subfield_codes_to_json_tags.empty() and json_tag.empty())
                LOG_ERROR("missing JSON source tag(s) for MARC field tag \"" + tag + "\" in section \"" + section_name + "\"!");
            if (not subfield_codes_to_json_tags.empty() and not json_tag.empty())
                 LOG_ERROR("can't have subfield and non-subfield contents for MARC field tag \"" + tag + "\" in section \""
                           + section_name + "\"!");
            const auto field_contents_prefix(section.getString("field_contents_prefix", ""));
            if (not field_contents_prefix.empty() and not subfield_codes_to_json_tags.empty())
                LOG_ERROR("can't specify a field contents prefix when subfields have been specified for MARC field tag \""
                          + tag + "\" in section \"" + section_name + "\"!");

            field_descriptors.emplace_back(section_name, tag, section.getString("overflow_tag", ""), section.getChar("indicator1", ' '),
                                           section.getChar("indicator2", ' '), section.getBool("repeat_field", false),
                                           subfield_codes_to_json_tags, subfield_codes_to_prefixes, subfield_codes_to_fixed_subfields,
                                           subfield_codes_to_extraction_regexes_map, json_tag, field_contents_prefix,
                                           section.getBool("map_to_marc_language_code", false), section.getBool("normalise_issn", false),
                                           section.getBool("required", false));
        }
    }

    std::sort(field_descriptors.begin(), field_descriptors.end());
    return field_descriptors;
}


enum ReferencedJSONDataState { NO_DATA_FOUND, ONLY_SCALAR_DATA_FOUND, ONLY_ARRAY_DATA_FOUND, SCALAR_AND_ARRAY_DATA_FOUND,
                               FOUND_AT_LEAST_ONE_OBJECT, INCONSISTENT_ARRAY_LENGTHS };


std::string ReferencedJSONDataStateToString(const ReferencedJSONDataState referenced_json_data_state) {
    switch (referenced_json_data_state) {
    case NO_DATA_FOUND:
        return "NO_DATA_FOUND";
    case ONLY_SCALAR_DATA_FOUND:
        return "ONLY_SCALAR_DATA_FOUND";
    case ONLY_ARRAY_DATA_FOUND:
        return "ONLY_ARRAY_DATA_FOUND";
    case SCALAR_AND_ARRAY_DATA_FOUND:
        return "SCALAR_AND_ARRAY_DATA_FOUND";
    case FOUND_AT_LEAST_ONE_OBJECT:
        return "FOUND_AT_LEAST_ONE_OBJECT";
    case INCONSISTENT_ARRAY_LENGTHS:
        return "INCONSISTENT_ARRAY_LENGTHS";
    }
}


ReferencedJSONDataState CategorizeJSONReferences(const std::shared_ptr<const JSON::ObjectNode> &object,
                                                 const std::vector<std::pair<char, std::string>> &subfield_codes_to_json_tags,
                                                 size_t * const common_array_length)
{
    unsigned array_references_count(0), subfield_data_found_count(0);
    size_t last_array_length(std::numeric_limits<size_t>::max());
    for (const auto &subfield_code_and_json_tag : subfield_codes_to_json_tags) {
        const auto node(object->deepResolveNode(subfield_code_and_json_tag.second));
        if (node != nullptr) {
            ++subfield_data_found_count;
            if (node->getType() == JSON::JSONNode::OBJECT_NODE)
                return FOUND_AT_LEAST_ONE_OBJECT;

            if (node->getType() == JSON::JSONNode::ARRAY_NODE) {
                ++array_references_count;
                const size_t array_length(JSON::JSONNode::CastToArrayNodeOrDie("CategorizeJSONReferences", node)->size());
                if (last_array_length == std::numeric_limits<size_t>::max())
                    last_array_length = array_length;
                else if (last_array_length != array_length)
                    return INCONSISTENT_ARRAY_LENGTHS;
            }
        }
    }

    if (subfield_data_found_count == 0)
        return NO_DATA_FOUND;
    if (array_references_count == 0)
        return ONLY_SCALAR_DATA_FOUND;
    if (array_references_count == subfield_data_found_count) {
        *common_array_length = last_array_length;
        return ONLY_ARRAY_DATA_FOUND;
    }
    return SCALAR_AND_ARRAY_DATA_FOUND;
}


// We need this because StringNode's toString() does extra quoting.
std::string GetScalarJSONStringValueWithoutQuotes(const std::shared_ptr<const JSON::JSONNode> &node) {
    if (node->getType() != JSON::JSONNode::STRING_NODE)
        return node->toString();

    const auto string_node(JSON::JSONNode::CastToStringNodeOrDie("GetScalarJSONStringValueWithoutQuotes", node));
    return string_node->getValue();
}


// Returns the empty string if an entry for "subfield_code" was not found.
std::string FindMapEntryForSubfieldCode(const char subfield_code, const std::vector<std::pair<char, std::string>> &subfield_codes_to_values_map) {
    const auto subfield_code_and_value(std::find_if(subfield_codes_to_values_map.cbegin(), subfield_codes_to_values_map.cend(),
                                                    [&](const std::pair<char, std::string> &subfield_code_and_prefix)
                                                        { return subfield_code_and_prefix.first == subfield_code; }));
    return (subfield_code_and_value == subfield_codes_to_values_map.cend()) ? "" : subfield_code_and_value->second;
}


RegexMatcher *GetRegexMatcherOrNULL(const char subfield_code,
                                    const std::map<char, std::shared_ptr<RegexMatcher>> &subfield_codes_to_regex_matchers_map)
{
    const auto subfield_code_and_regex_matcher(subfield_codes_to_regex_matchers_map.find(subfield_code));
    return (subfield_code_and_regex_matcher == subfield_codes_to_regex_matchers_map.cend()) ? nullptr
                                                                                            : subfield_code_and_regex_matcher->second.get();
}


void UpdateISSNReferenceCount(const std::string &cleaned_up_json_value,
                              std::unordered_map<std::string, unsigned> * const issns_to_counts_map)
{
    auto issn_and_count(issns_to_counts_map->find(cleaned_up_json_value));
    if (issn_and_count == issns_to_counts_map->end())
        (*issns_to_counts_map)[cleaned_up_json_value] = 1;
    else
        ++(issn_and_count->second);
}


static unsigned matched_issn_count, not_matched_issn_count;


// \return True if a subfield was inserted into "record" and false o/w.
// \note   "array_index" is only used if the node lookup in this function results in a JSON array.
bool ExtractJSONAndGenerateSubfields(MARC::Record * const record, const MARC::Tag &tag, const FieldDescriptor &field_descriptor,
                                     const std::unordered_map<std::string, JournalTitleAndPPN> &issns_to_journal_titles_and_ppns_map,
                                     const std::shared_ptr<const JSON::ObjectNode> &object, const size_t json_array_index,
                                     std::unordered_map<std::string, unsigned> * const issns_to_counts_map)
{
    MARC::Record::Field new_field(tag);
    bool created_at_least_one_subfield(false);

    for (const auto &subfield_code_and_json_tag : field_descriptor.subfield_codes_to_json_tags_) {
        auto scalar_or_array_node(object->deepResolveNode(subfield_code_and_json_tag.second));
        if (scalar_or_array_node == nullptr)
            continue;

        // If we have an arry node we need to go one level deeper into the JSON structure:
        if (scalar_or_array_node->getType() == JSON::JSONNode::ARRAY_NODE) {
            const auto array_node(JSON::JSONNode::CastToArrayNodeOrDie("array_node", scalar_or_array_node));
            scalar_or_array_node = array_node->getNode(json_array_index);
        }

        const std::string subfield_prefix(FindMapEntryForSubfieldCode(subfield_code_and_json_tag.first,
                                                                      field_descriptor.subfield_codes_to_prefixes_));
        std::string extracted_value(GetScalarJSONStringValueWithoutQuotes(scalar_or_array_node));

        const auto regex_matcher(GetRegexMatcherOrNULL(subfield_code_and_json_tag.first,
                                                       field_descriptor.subfield_codes_to_extraction_regexes_map_));
        if (regex_matcher != nullptr) {
            if (not regex_matcher->matched(extracted_value))
                continue;
            extracted_value = (*regex_matcher)[0];
        }

        if (field_descriptor.map_to_marc_language_code_) {
            const std::string original_value(extracted_value);
            extracted_value = MARC::MapToMARCLanguageCode(extracted_value);
            if (extracted_value.empty()) {
                LOG_WARNING("can't map \"" + original_value + "\" to a MARC language code!");
                continue;
            }
        }

        if (field_descriptor.normalise_issn_) {
            std::string normalised_issn;
            if (MiscUtil::NormaliseISSN(extracted_value, &normalised_issn))
                extracted_value = normalised_issn;
        }

        // ISSN processing:
        if (StringUtil::FindCaseInsensitive(field_descriptor.name_, "ISSN") != std::string::npos) {
            UpdateISSNReferenceCount(extracted_value, issns_to_counts_map);
            const auto issn_and_journal_title_and_ppn(issns_to_journal_titles_and_ppns_map.find(extracted_value));
            if (issn_and_journal_title_and_ppn == issns_to_journal_titles_and_ppns_map.cend())
                ++not_matched_issn_count;
            else {
                MARC::Record::Field _773_field(MARC::Tag("773"));
                _773_field.appendSubfield('t', issn_and_journal_title_and_ppn->second.journal_title_);
                if (not issn_and_journal_title_and_ppn->second.ppn_.empty())
                    _773_field.appendSubfield('w', "(DE-657)" + issn_and_journal_title_and_ppn->second.ppn_);
                _773_field.appendSubfield('x', extracted_value); // ISSN subfield
                record->insertField(_773_field);
                ++matched_issn_count;
            }
        }

        new_field.appendSubfield(subfield_code_and_json_tag.first, subfield_prefix + extracted_value);
        created_at_least_one_subfield = true;
    }

    if (created_at_least_one_subfield) {
        for (const auto &subfield_code_and_fixed_subfield : field_descriptor.subfield_codes_to_fixed_subfields_)
            new_field.appendSubfield(subfield_code_and_fixed_subfield.first, subfield_code_and_fixed_subfield.second);
        record->insertField(new_field);
        return true;
    }

    return false;
}


void ProcessFieldDescriptor(const FieldDescriptor &field_descriptor,
                            const std::unordered_map<std::string, JournalTitleAndPPN> &issns_to_journal_titles_and_ppns_map,
                            const std::shared_ptr<const JSON::ObjectNode> &object,
                            std::unordered_map<std::string, unsigned> * const issns_to_counts_map,
                            MARC::Record * const record)
{
    LOG_DEBUG("Processing " + field_descriptor.name_);
    bool created_at_least_one_field(false);
    if (not field_descriptor.json_tag_.empty()) { // Control field
        const auto node(object->deepResolveNode(field_descriptor.json_tag_));
        if (node != nullptr) {
            if (node->getType() == JSON::JSONNode::ARRAY_NODE)
                LOG_ERROR("no implemented support for control fields if the JSON data source is an array!");

            record->insertField(MARC::Tag(field_descriptor.tag_), GetScalarJSONStringValueWithoutQuotes(node));
            created_at_least_one_field = true;
        } else if (field_descriptor.required_)
            LOG_ERROR("missing JSON tag \"" + field_descriptor.json_tag_ + "\" for required field \"" + field_descriptor.name_ + "\"!");
    } else { // Data field
        size_t array_length;
        const auto referenced_json_data_state(CategorizeJSONReferences(object, field_descriptor.subfield_codes_to_json_tags_, &array_length));
        LOG_DEBUG("\t" + ReferencedJSONDataStateToString(referenced_json_data_state));
        if (referenced_json_data_state == NO_DATA_FOUND)
            goto final_processing;

        if (referenced_json_data_state == SCALAR_AND_ARRAY_DATA_FOUND)
            LOG_ERROR("mixed scalar and array data found for \"" + field_descriptor.name_ + "\"!");
        if (referenced_json_data_state == INCONSISTENT_ARRAY_LENGTHS)
            LOG_ERROR("JSON arrays of inconsistent lengths found for \"" + field_descriptor.name_ + "\"!");
        if (referenced_json_data_state == FOUND_AT_LEAST_ONE_OBJECT)
            LOG_ERROR("at least some object data found for \"" + field_descriptor.name_ + "\"!");

        if (referenced_json_data_state == ONLY_SCALAR_DATA_FOUND)
            created_at_least_one_field = ExtractJSONAndGenerateSubfields(record, field_descriptor.tag_, field_descriptor,
                                                                         issns_to_journal_titles_and_ppns_map, object, /* json_array_index = */-1,
                                                                         issns_to_counts_map);
        else { // All our data resides in JSON arrays.
            for (unsigned json_array_index(0); json_array_index < array_length; ++json_array_index) {
                std::string tag(field_descriptor.tag_);
                if (json_array_index > 0 and not field_descriptor.overflow_tag_.empty())
                    tag = field_descriptor.overflow_tag_;
                if (ExtractJSONAndGenerateSubfields(record, tag, field_descriptor, issns_to_journal_titles_and_ppns_map, object,
                                                    json_array_index, issns_to_counts_map))
                    created_at_least_one_field = true;
            }
        }
    }

final_processing:
    if (field_descriptor.required_ and not created_at_least_one_field)
        LOG_WARNING("required entry for \"" + field_descriptor.name_ + "\" not found!");
}


// \return True if we generated a MARC record or false if we suppressed the generation due to a duplicate unique ID.
bool GenerateSingleMARCRecordFromJSON(const std::shared_ptr<const JSON::ObjectNode> &object,
                                      const JSONNodeToBibliographicLevelMapper &json_node_to_bibliographic_level_mapper,
                                      const std::vector<FieldDescriptor> &field_descriptors,
                                      const std::unordered_map<std::string, JournalTitleAndPPN> &issns_to_journal_titles_and_ppns_map,
                                      MARC::Writer * const marc_writer, const bool extract_and_count_issns_only,
                                      std::unordered_map<std::string, unsigned> * const issns_to_counts_map,
                                      const bool ignore_unique_id_dups, KeyValueDB * const unique_id_to_date_map)
{
    std::string control_number;
    const auto descriptor_for_field_001(std::find_if(field_descriptors.begin(), field_descriptors.end(),
                                                     [](const FieldDescriptor &descriptor){ return descriptor.tag_ == "001"; }));
    if (descriptor_for_field_001 != field_descriptors.end()) {
        control_number = object->getOptionalStringValue(descriptor_for_field_001->json_tag_);
        if (not control_number.empty())
            control_number = descriptor_for_field_001->field_contents_prefix_ + control_number;
        else
            LOG_ERROR("missing unique ID! We do need a basis for the generation of a control number!");
    }

    if (not extract_and_count_issns_only and (not ignore_unique_id_dups and unique_id_to_date_map->keyIsPresent(control_number)))
        return false;

    const auto bibliographic_level(json_node_to_bibliographic_level_mapper.getBibliographicLevel(*object));
    MARC::Record new_record(MARC::Record::TypeOfRecord::LANGUAGE_MATERIAL, bibliographic_level, control_number);
    for (const auto field_descriptor : field_descriptors) {
        if (field_descriptor.tag_ != "001")
            ProcessFieldDescriptor(field_descriptor, issns_to_journal_titles_and_ppns_map, object, issns_to_counts_map, &new_record);
    }
    if (not extract_and_count_issns_only)
        marc_writer->write(new_record);
    unique_id_to_date_map->addOrReplace(control_number, TimeUtil::GetCurrentDateAndTime());

    return not extract_and_count_issns_only;
}


void GenerateMARCFromJSON(const std::shared_ptr<const JSON::JSONNode> &object_or_array_root,
                          const JSONNodeToBibliographicLevelMapper &json_node_to_bibliographic_level_mapper,
                          const std::vector<FieldDescriptor> &field_descriptors,
                          const std::unordered_map<std::string, JournalTitleAndPPN> &issns_to_journal_titles_and_ppns_map,
                          MARC::Writer * const marc_writer,
                          const bool extract_and_count_issns_only,
                          std::unordered_map<std::string, unsigned> * const issns_to_counts_map,
                          const bool ignore_unique_id_dups, KeyValueDB * const unique_id_to_date_map)
{
    unsigned created_count(0), duplicate_skipped_count(0);

    switch (object_or_array_root->getType()) {
    case JSON::JSONNode::OBJECT_NODE:
        if (GenerateSingleMARCRecordFromJSON(JSON::JSONNode::CastToObjectNodeOrDie("object_or_array_root", object_or_array_root),
                                             json_node_to_bibliographic_level_mapper, field_descriptors,
                                             issns_to_journal_titles_and_ppns_map, marc_writer,
                                             extract_and_count_issns_only, issns_to_counts_map,
                                             ignore_unique_id_dups, unique_id_to_date_map))
            ++created_count;
        else
            ++duplicate_skipped_count;
        break;
    case JSON::JSONNode::ARRAY_NODE: {
        const auto array_node(JSON::JSONNode::CastToArrayNodeOrDie("object_or_array_root", object_or_array_root));
        for (const auto &array_element : *array_node) {
            if (GenerateSingleMARCRecordFromJSON(JSON::JSONNode::CastToObjectNodeOrDie("array_element", array_element),
                                                 json_node_to_bibliographic_level_mapper, field_descriptors,
                                                 issns_to_journal_titles_and_ppns_map, marc_writer,
                                                 extract_and_count_issns_only, issns_to_counts_map,
                                                 ignore_unique_id_dups, unique_id_to_date_map))
                ++created_count;
            else
                ++duplicate_skipped_count;
        }
        break;
    }
    default:
        LOG_ERROR("\"root_path\" in section \"Gobal\" does not reference a JSON object or array!");
    }

    LOG_INFO("created " + std::to_string(created_count) + " MARC record(s) and skipped "  + std::to_string(duplicate_skipped_count) + " duplicate(s).");
    LOG_INFO(std::to_string(matched_issn_count) + " of " + std::to_string(matched_issn_count + not_matched_issn_count)
             + " encountered ISSN's were resolved and those records were linked to their respective serials.");
}


const std::string UNIQUE_ID_TO_DATE_MAP_PATH(UBTools::GetTuelibPath() + "convert_json_to_marc.db");


} // namespace


int Main(int argc, char **argv) {
    if (argc != 4 and argc != 5)
        Usage();

        if (std::strcmp(argv[1], "--create-unique-id-db") == 0) {
        KeyValueDB::Create(UNIQUE_ID_TO_DATE_MAP_PATH);
        --argc, ++argv;
    }

    bool ignore_unique_id_dups(false);
    if (std::strcmp(argv[1], "--ignore-unique-id-dups") == 0) {
        ignore_unique_id_dups = true;
        --argc, ++argv;
    }

    bool extract_and_count_issns_only(false);
    if (std::strcmp(argv[1], "--extract-and-count-issns-only") == 0) {
        extract_and_count_issns_only = true;
        --argc, ++argv;
    }

    if ((extract_and_count_issns_only and argc != 3) or (not extract_and_count_issns_only and argc != 4))
        Usage();

    std::unordered_map<std::string, JournalTitleAndPPN> issns_to_journal_titles_and_ppns_map;
    LoadISSNsToJournalTitlesAndPPNsMap(&issns_to_journal_titles_and_ppns_map);

    std::string root_path;
    std::unique_ptr<JSONNodeToBibliographicLevelMapper> json_node_to_bibliographic_level_mapper;
    const auto field_descriptors(LoadFieldDescriptors(argv[1], &root_path, &json_node_to_bibliographic_level_mapper));

    const std::string json_file_path(argv[2]);
    const auto json_source(FileUtil::ReadStringOrDie(json_file_path));
    JSON::Parser parser(json_source);
    std::shared_ptr<JSON::JSONNode> tree_root;
    if (not parser.parse(&tree_root))
        LOG_ERROR("Failed to parse the contents of \"" + json_file_path + "\": " + parser.getErrorMessage());
    const auto object_or_array_root(JSON::LookupNode(root_path, tree_root));

    KeyValueDB unique_id_to_date_map(UNIQUE_ID_TO_DATE_MAP_PATH);
    std::unordered_map<std::string, unsigned> issns_to_counts_map;
    const std::unique_ptr<MARC::Writer> marc_writer(extract_and_count_issns_only ? nullptr : MARC::Writer::Factory(argv[3]));
    GenerateMARCFromJSON(object_or_array_root, *json_node_to_bibliographic_level_mapper, field_descriptors,
                         issns_to_journal_titles_and_ppns_map, marc_writer.get(), extract_and_count_issns_only,
                         &issns_to_counts_map, ignore_unique_id_dups, &unique_id_to_date_map);

    if (extract_and_count_issns_only) {
        std::vector<std::pair<std::string, unsigned>> issns_and_counts;
        issns_and_counts.reserve(issns_to_counts_map.size());
        for (const auto &issn_and_count : issns_to_counts_map)
            issns_and_counts.emplace_back(issn_and_count);
        std::sort(issns_and_counts.begin(), issns_and_counts.end(),
                  [](const auto &a, const auto &b) { return a.second > b.second; });
        for (const auto &issn_and_count : issns_and_counts)
            std::cout << issn_and_count.first << '\t' << issn_and_count.second << '\n';
    }

    return EXIT_SUCCESS;
}
