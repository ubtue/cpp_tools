/** \file    crossref_downloader.cc
 *  \brief   Downloads metadata from crossref.org and generates MARC-21 records.
 *  \author  Dr. Johannes Ruscheinski
 *
 *  \copyright (C) 2017, Library of the University of Tübingen
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
#include <stdexcept>
#include <vector>
#include <cstdlib>
#include <cstring>
#include <boost/property_tree/ptree.hpp>
#include <boost/property_tree/json_parser.hpp>
#include "Compiler.h"
#include "Downloader.h"
#include "FileUtil.h"
#include "MarcRecord.h"
#include "MarcWriter.h"
#include "StringUtil.h"
#include "TextUtil.h"
#include "UrlUtil.h"
#include "util.h"


void Usage() {
    std::cerr << "Usage: " << ::progname << " [--timeout seconds] journal_list crossref_to_marc_mapping marc_output\n";
    std::exit(EXIT_FAILURE);
}


/** \class MapDescriptor
 *  \brief Describes a mapping from a Crossref JSON field to a MARC-21 field.
 */
class MapDescriptor {
public:
    enum FieldType { STRING, AUTHOR_VECTOR, STRING_VECTOR };
private:
    std::string json_field_;
    FieldType field_type_;
    std::string marc_subfield_;
public:
    MapDescriptor(const std::string &json_field, const FieldType field_type, const std::string &marc_subfield)
        : json_field_(json_field), field_type_(field_type), marc_subfield_(marc_subfield) { }
    inline const std::string &getJsonField() const { return json_field_; }
    inline FieldType getFieldType() const { return field_type_; }
    inline const std::string &getMarcSubfield() const { return marc_subfield_; }

    /** \return True if we found a matching field type, otherwise false. */
    static bool MapStringToFieldType(const std::string &field_type_candidate, FieldType * const field_type);
};


bool MapDescriptor::MapStringToFieldType(const std::string &field_type_candidate, FieldType * const field_type) {
    if (field_type_candidate == "string") {
        *field_type = STRING;
        return true;
    }

    if (field_type_candidate == "author_vector") {
        *field_type = AUTHOR_VECTOR;
        return true;
    }

    if (field_type_candidate == "string_vector") {
        *field_type = STRING_VECTOR;
        return true;
    }

    return false;
}


void ParseSingleMapping(const std::string &line, const unsigned line_no, std::string * const json_field,
                        MapDescriptor::FieldType * const field_type, std::string * const marc_subfield)
{
    const size_t arrow_start_pos(line.find("->"));
    if (unlikely(arrow_start_pos == std::string::npos))
        Error("Crossref-to-MARC mapping missing \"->\" on line #" + std::to_string(line_no) + "!");

    *json_field = line.substr(0, arrow_start_pos - 1);
    StringUtil::TrimWhite(json_field);
    if (unlikely(json_field->empty()))
        Error("Crossref-to-MARC mapping missing JSON field name on line #" + std::to_string(line_no) + "!");

    std::vector<std::string> parts;
    if (unlikely(StringUtil::SplitThenTrimWhite(line.substr(arrow_start_pos + 2), ',', &parts) != 2))
        Error("Crossref-to-MARC mapping malformed line #" + std::to_string(line_no) + "!");

    if (unlikely(not MapDescriptor::MapStringToFieldType(parts[0], field_type)))
        Error("Crossref-to-MARC mapping contains invalid field type \"" + parts[0] + "\" on line #"
              + std::to_string(line_no) + "!");

    if (unlikely(parts[1].length() != 4))
        Error("Crossref-to-MARC mapping contains a bad MARC-21 subfield specification \"" + parts[1] + "\" on line #"
              + std::to_string(line_no) + "!");
    *marc_subfield = parts[1];
}


void ParseCrossrefToMarcMapping(File * const input, std::vector<MapDescriptor> * const map_descriptors) {
    unsigned line_no(0);
    while (not input->eof()) {
        std::string line;
        input->getline(&line);
        ++line_no;
        StringUtil::Trim(&line);
        if (line.empty())
            continue;

        std::string json_field, marc_subfield;
        MapDescriptor::FieldType field_type;
        ParseSingleMapping(line, line_no, &json_field, &field_type, &marc_subfield);
        map_descriptors->emplace_back(json_field, field_type, marc_subfield);
    }

    std::cout << "Read " << map_descriptors->size() << " mappings from Crossref JSON fields to MARC-21 fields.\n";
}


// Compares "s1" and "s2" while ignoring any occurences of characters found in "ignore_chars".
bool EqualIgnoreChars(const std::string &s1, const std::string &s2, const std::string &ignore_chars) {
    auto ch1(s1.cbegin());
    auto ch2(s2.cbegin());
    while (ch1 != s1.cend() and ch2 != s2.cend()) {
        if (ignore_chars.find(*ch1) != std::string::npos)
            ++ch1;
        else if (ignore_chars.find(*ch2) != std::string::npos)
            ++ch2;
        else if (*ch1 != *ch2)
            return false;
        else
            ++ch1, ++ch2;
    }

    while (ch1 != s1.cend() and ignore_chars.find(*ch1) != std::string::npos)
        ++ch1;
    while (ch2 != s2.cend() and ignore_chars.find(*ch2) != std::string::npos)
        ++ch2;

    return ch1 == s1.cend() and ch2 == s2.cend();
}


bool FuzzyTextMatch(const std::string &s1, const std::string &s2) {
    std::string lowercase_s1;
    if (unlikely(not TextUtil::UTF8ToLower(s1, &lowercase_s1)))
        Error("failed to convert supposed UTF-8 string \"" + s1 + "\" to a wide-character string! (1)");

    std::string lowercase_s2;
    if (unlikely(not TextUtil::UTF8ToLower(s2, &lowercase_s2)))
        Error("failed to convert supposed UTF-8 string \"" + s2 + "\" to a wide-character string! (2)");

    static const std::string IGNORE_CHARS(" :-");
    return EqualIgnoreChars(lowercase_s1, lowercase_s2, IGNORE_CHARS);
}


std::vector<std::string> ExtractString(const boost::property_tree::ptree &message_tree,
                                       const std::string &json_field_name)
{
    std::vector<std::string> extracted_values;
    const std::string value(message_tree.get<std::string>(json_field_name, ""));
    if (not value.empty())
        extracted_values.emplace_back(value);

    return extracted_values;
}


std::string ExtractAuthor(const boost::property_tree::ptree &author_ptree) {
    std::string author(author_ptree.get<std::string>("family"));
    const std::string given_name(author_ptree.get<std::string>("given", ""));
    if (not given_name.empty())
        author += ", " + given_name;

    return author;
}


std::vector<std::string> ExtractAuthorVector(const boost::property_tree::ptree &message_tree,
                                             const std::string &json_field_name)
{
    std::vector<std::string> extracted_values;

    boost::property_tree::ptree::const_assoc_iterator array_iter(message_tree.find(json_field_name));
    if (array_iter != message_tree.not_found()) {
        for (const auto &array_entry : array_iter->second)
            extracted_values.emplace_back(ExtractAuthor(array_entry.second));
    }

    return extracted_values;
}


std::vector<std::string> ExtractStringVector(const boost::property_tree::ptree &message_tree,
                                             const std::string &json_field_name)
{
    std::vector<std::string> extracted_values;

    boost::property_tree::ptree::const_assoc_iterator array_iter(message_tree.find(json_field_name));
    if (array_iter != message_tree.not_found()) {
        for (const auto &array_entry : array_iter->second)
            extracted_values.emplace_back(array_entry.second.data());
    }

    return extracted_values;
}


void CreateAndWriteMarcRecord(MarcWriter * const marc_writer, const boost::property_tree::ptree &message_tree,
                              const std::vector<MapDescriptor> &map_descriptors)
{
    MarcRecord record;
    record.getLeader().setBibliographicLevel('a'); // We have an article.
    static unsigned control_number(0);
    record.insertField("001", std::to_string(++control_number));

    for (const auto &map_descriptor : map_descriptors) {
        std::vector<std::string> field_values;
        switch (map_descriptor.getFieldType()) {
        case MapDescriptor::STRING:
            field_values = ExtractString(message_tree, map_descriptor.getJsonField());
            break;
        case MapDescriptor::AUTHOR_VECTOR:
            field_values = ExtractAuthorVector(message_tree, map_descriptor.getJsonField());
            break;
        case MapDescriptor::STRING_VECTOR:
            field_values = ExtractStringVector(message_tree, map_descriptor.getJsonField());
            break;
        default:
            Error("in CreateAndWriteMarcRecord: unexpected field type!");
        }

        const std::string tag(map_descriptor.getMarcSubfield().substr(0, DirectoryEntry::TAG_LENGTH));
        const char subfield_code(map_descriptor.getMarcSubfield().back());
        for (const auto field_value : field_values)
            record.insertSubfield(tag, subfield_code, field_value);
    }

    marc_writer->write(record);
}


// Converts the nnnn part of \unnnn to UTF-8. */
std::string UTF16EscapeToUTF8(std::string::const_iterator &cp, const std::string::const_iterator &end) {
    std::string hex_codes;
    for (unsigned i(0); i < 4; ++i) {
        if (unlikely(cp == end))
            Error("in UTF16EscapeToUTF8: unexpected end of input!");
        hex_codes += *cp++;
    }

    uint16_t u1;
    if (unlikely(not StringUtil::ToUnsignedShort(hex_codes, &u1, 16)))
            Error("in UTF16EscapeToUTF8: invalid hex sequence \\u" + hex_codes + "! (1)");

    if (TextUtil::IsValidSingleUTF16Char(u1))
        return TextUtil::UTF32ToUTF8(TextUtil::UTF16ToUTF32(u1));

    if (unlikely(not TextUtil::IsFirstHalfOfSurrogatePair(u1)))
        Error("in UTF16EscapeToUTF8: \\u" + hex_codes + " is neither a standalone UTF-8 character nor a valid "
              "first half of a UTF-16 surrogate pair!");

    if (unlikely(cp == end or *cp++ != '\\'))
        Error("in UTF16EscapeToUTF8: could not find expected '\\' as part of the 2nd half of a surrogate pair!");
    if (unlikely(cp == end or *cp++ != 'u'))
        Error("in UTF16EscapeToUTF8: could not find expected 'u' as part of the 2nd half of a surrogate pair!");
    
    hex_codes.clear();
    for (unsigned i(0); i < 4; ++i) {
        if (unlikely(cp == end))
            Error("in UTF16EscapeToUTF8: unexpected end of input while attempting to read a 2nd half of a surrogate "
                  "pair!");
        hex_codes += *cp++;
    }

    uint16_t u2;
    if (unlikely(not StringUtil::ToUnsignedShort(hex_codes, &u2, 16)))
            Error("in UTF16EscapeToUTF8: invalid hex sequence \\u" + hex_codes + "! (2)");
    if (unlikely(not TextUtil::IsSecondHalfOfSurrogatePair(u2)))
            Error("in UTF16EscapeToUTF8: invalid 2nd half of a surrogate pair: \\u" + hex_codes + "!");

    return TextUtil::UTF32ToUTF8(TextUtil::UTF16ToUTF32(u1, u2));
}


std::string UnescapeCrossRefJSON(const std::string &json_text) {
    std::string unescaped_string;
    bool in_text(false);
    auto cp(json_text.cbegin());
    while (cp != json_text.cend()) {
        if (in_text) {
            if (*cp == '\\') {
                if (unlikely(cp + 1 == json_text.cend()))
                    Error("in UnescapeCrossRefJSON: malformed JSON!");
                ++cp;
                if (*cp == '/')
                    unescaped_string += *cp++;
                else if (*cp == 'u')
                    unescaped_string += UTF16EscapeToUTF8(++cp, json_text.cend());
                else {
                    unescaped_string += '\\';
                    Warning("in UnescapeCrossRefJSON: unexpected escape \\" + std::string(1, *cp)
                            + "in JSON string constant!");
                    unescaped_string += *cp++;
                }
            } else {
                if (*cp == '"')
                    in_text = false;
                unescaped_string += *cp++;
            }
        } else {
            in_text = *cp == '"';
            unescaped_string += *cp++;
        }
    }

    return unescaped_string;
}


bool ProcessJournal(const unsigned timeout, const std::string &journal_name, MarcWriter * const marc_writer,
                    const std::vector<MapDescriptor> &map_descriptors)
{
        std::string json_document;
        if (Download("https://search.crossref.org/dois?q=" + UrlUtil::UrlEncode(journal_name), timeout,
                     &json_document) != 0)
            return false;

        std::stringstream query_input(json_document, std::ios_base::in);
        boost::property_tree::ptree query_property_tree;
        boost::property_tree::json_parser::read_json(query_input, query_property_tree);

        unsigned document_count(0);
        for (const auto &array_entry : query_property_tree) {
            const std::string doi_url(array_entry.second.get_child("doi").data());
            
            if (Download("https://api.crossref.org/v1/works/" + UrlUtil::UrlEncode(doi_url), timeout,
                         &json_document) != 0)
                continue;
            json_document = UnescapeCrossRefJSON(json_document);
            
            std::stringstream record_input(json_document, std::ios_base::in);
            boost::property_tree::ptree record_property_tree;
            boost::property_tree::json_parser::read_json(record_input, record_property_tree);

            boost::property_tree::ptree::const_assoc_iterator message_iter(record_property_tree.find("message"));
            if (unlikely(message_iter == record_property_tree.not_found())) {
                Warning("JSON document is missing a top-level \"message\" field!");
                continue;
            }

            boost::property_tree::ptree message_sub_tree(message_iter->second);
            if (message_sub_tree.get<std::string>("type") != "journal-article")
                continue;

            const boost::property_tree::ptree::const_assoc_iterator container_titles(
                message_sub_tree.find("container-title"));
            if (container_titles == record_property_tree.not_found())
                continue;

            bool matched_at_least_one(false);
            for (const auto container_title_node : container_titles->second) {
                if (FuzzyTextMatch(journal_name, container_title_node.second.data())) {
                    matched_at_least_one = true;
                    break;
                }
            }
            if (not matched_at_least_one)
                continue;

            CreateAndWriteMarcRecord(marc_writer, message_sub_tree, map_descriptors);
            ++document_count;
        }

        return document_count > 0;
}


int main(int argc, char *argv[]) {
    ::progname = argv[0];

    if (argc != 4 and argc != 6)
        Usage();

    const unsigned DEFAULT_TIMEOUT(20); // seconds
    unsigned timeout(DEFAULT_TIMEOUT);
    if (std::strcmp(argv[1], "--timeout") == 0) {
        if (not StringUtil::ToUnsigned(argv[2], &timeout))
            Error("bad timeout \"" + std::string(argv[2]) + "\"!");
        argc -= 2;
        argv += 2;
    }

    if (argc != 4)
        Usage();

    const std::string journal_list_filename(argv[1]);
    const std::string crossref_to_marc_mapping_filename(argv[2]);
    const std::string marc_output_filename(argv[3]);

    try {
        const std::unique_ptr<File> journal_list_file(FileUtil::OpenInputFileOrDie(journal_list_filename));
        const std::unique_ptr<File> crossref_to_marc_mapping_file(
            FileUtil::OpenInputFileOrDie(crossref_to_marc_mapping_filename));
        const std::unique_ptr<MarcWriter> marc_writer(MarcWriter::Factory(marc_output_filename));

        std::vector<MapDescriptor> map_descriptors;
        ParseCrossrefToMarcMapping(crossref_to_marc_mapping_file.get(), &map_descriptors);

        unsigned success_count(0);
        while (not journal_list_file->eof()) {
            std::string line;
            journal_list_file->getline(&line);
            StringUtil::Trim(&line);
            if (not line.empty() and ProcessJournal(timeout, line, marc_writer.get(), map_descriptors))
                ++success_count;
        }

        std::cout << "Downloaded metadata for at least one article from " << success_count << " journals.\n";
        return success_count == 0 ? EXIT_FAILURE : EXIT_SUCCESS;
    } catch (const std::exception &e) {
        Error("Caught exception: " + std::string(e.what()));
    }
}
