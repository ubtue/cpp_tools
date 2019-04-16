// A tool for adding keywords extracted from titles to MARC records.
/*
    Copyright (C) 2015-2019, Library of the University of Tübingen

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
#include <fstream>
#include <iostream>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <unordered_set>
#include <cassert>
#include <cstdlib>
#include <cstring>
#include "MARC.h"
#include "RegexMatcher.h"
#include "Stemmer.h"
#include "StringUtil.h"
#include "TextUtil.h"
#include "util.h"


namespace {


[[noreturn]] void Usage() {
    std::cerr << "Usage: " << ::progname << " marc_input marc_output [stopwords_files]\n";
    std::cerr << "       The MARC-21 output will have enriched keywords based on title words that were\n";
    std::cerr << "       similar to keywords found in the MARC-21 input file.\n";
    std::cerr << "       Stopword files must be named \"stopwords.xxx\" where xxx has to be a 3-letter\n";
    std::cerr << "       language code.\n";
    std::exit(EXIT_FAILURE);
}


void LoadStopwords(File * const input, const std::string &language_code, std::unordered_set<std::string> * const stopwords_set) {
    LOG_INFO("Starting loading of stopwords for language: " + language_code);

    unsigned count(0);
    while (not input->eof()) {
        const std::string line(input->getline());
        if (line.empty() or line[0] == ';') // Empty or comment line?
            continue;

        std::string word(TextUtil::UTF8ToLower(line));
        stopwords_set->insert(TextUtil::UTF8ToLower(line));
        ++count;
    }

    LOG_INFO("Read " + std::to_string(count) + " stopwords.");
}


void FilterOutStopwords(const std::unordered_set<std::string> &stopwords,
                        std::vector<std::string> * const words)
{
    std::vector<std::string> filtered_words;
    bool removed_at_least_one_word(false);
    for (const auto &word : *words) {
      if (stopwords.find(word) == stopwords.end())
          filtered_words.emplace_back(word);
      else
          removed_at_least_one_word = true;
    }
    if (removed_at_least_one_word)
        words->swap(filtered_words);
}


std::string VectorToString(const std::vector<std::string> &v) {
    std::string vector_as_string;
    for (std::vector<std::string>::const_iterator entry(v.cbegin()); entry != v.cend(); ++entry) {
        vector_as_string += *entry;
        if ((entry + 1) != v.cend())
            vector_as_string += ' ';
    }
    return vector_as_string;
}


auto constexpr MIN_WORD_LENGTH(3); // At least this many characters have to be in a word for to consider it
                                   // to be "interesting".


inline std::string FilterOutNonwordChars(const std::string &phrase) {
    std::vector<std::string> phrase_as_vector;
    TextUtil::ChopIntoWords(phrase, &phrase_as_vector, MIN_WORD_LENGTH);
    return VectorToString(phrase_as_vector);
}


// Lowercases and stems "keyword_phrase" and chops it into `words'.  Populates
// "stemmed_keyword_to_stemmed_keyphrases_map" and "stemmed_keyphrases_to_unstemmed_keyphrases_map".
// The former maps from each individual stemmed word to the entire cleaned up and stemmed key phrase and the
// latter maps from the cleaned up and stemmed key phrase to the original key phrase.
void ProcessKeywordPhrase(
    const std::string &keyword_phrase, const Stemmer * const stemmer,
    std::unordered_map<std::string, std::set<std::string>> * const stemmed_keyword_to_stemmed_keyphrases_map,
    std::unordered_map<std::string, std::string> * const stemmed_keyphrases_to_unstemmed_keyphrases_map)
{
    std::string cleaned_up_phrase(keyword_phrase);

    // Convert "surname, first_name" to "first_name surname" assuming we only have a comma if the keyphrase
    // consist of a name:
    const size_t comma_pos(keyword_phrase.find(','));
    if (comma_pos != std::string::npos)
        cleaned_up_phrase = cleaned_up_phrase.substr(comma_pos + 1) + " "
            + cleaned_up_phrase.substr(0, comma_pos);

    cleaned_up_phrase = FilterOutNonwordChars(cleaned_up_phrase);

    const std::string stemmed_phrase(stemmer == nullptr ? cleaned_up_phrase : stemmer->stem(cleaned_up_phrase));
    std::string lowercase_stemmed_phrase;
    TextUtil::UTF8ToLower(stemmed_phrase, &lowercase_stemmed_phrase);
    (*stemmed_keyphrases_to_unstemmed_keyphrases_map)[lowercase_stemmed_phrase] = keyword_phrase;
    std::vector<std::string> stemmed_words;
    StringUtil::Split(lowercase_stemmed_phrase, ' ', &stemmed_words, /* suppress_empty_components = */true);
    for (const auto &stemmed_word : stemmed_words) {
        auto iter(stemmed_keyword_to_stemmed_keyphrases_map->find(stemmed_word));
        if (iter == stemmed_keyword_to_stemmed_keyphrases_map->end())
            (*stemmed_keyword_to_stemmed_keyphrases_map)[stemmed_word] =
                std::set<std::string>{ lowercase_stemmed_phrase, };
        else
            (*stemmed_keyword_to_stemmed_keyphrases_map)[stemmed_word].insert(lowercase_stemmed_phrase);
    }
}


// Replace patterns like "Jahrhundert XX" w/ "XX. Jahrhundert" etc.  If we don't have a match we
// return the original string.
std::string CanonizeCentury(const std::string &century_candidate) {
    static RegexMatcher *matcher(RegexMatcher::RegexMatcherFactory("[jJ]ahrhundert (\\d+)\\.?"));
    if (not matcher->matched(century_candidate))
        return century_candidate;

    std::string ordinal(century_candidate.substr(12));
    if (ordinal[ordinal.size() - 1] != '.')
        ordinal += '.';

    return ordinal + " " + century_candidate.substr(0, 12);
}


size_t ExtractKeywordsFromKeywordChainFields(
    const MARC::Record &record,
    const Stemmer * const stemmer,
    std::unordered_map<std::string, std::set<std::string>> * const stemmed_keyword_to_stemmed_keyphrases_map,
    std::unordered_map<std::string, std::string> * const stemmed_keyphrases_to_unstemmed_keyphrases_map)
{
    size_t keyword_count(0);

    for (const auto &field : record.getTagRange("689")) {
        const auto subfields(field.getSubfields());
        const std::string subfield_a_value(subfields.getFirstSubfieldWithCode('a'));
        if (not subfield_a_value.empty()) {
            std::string keyphrase(subfield_a_value);
            const std::string subfield_c_value(subfields.getFirstSubfieldWithCode('c'));
            if (not subfield_c_value.empty())
                keyphrase += " " + subfield_c_value;
            ProcessKeywordPhrase(CanonizeCentury(keyphrase), stemmer, stemmed_keyword_to_stemmed_keyphrases_map,
                                 stemmed_keyphrases_to_unstemmed_keyphrases_map);
            ++keyword_count;
        }
    }

    return keyword_count;
}


size_t ExtractAllKeywords(
    const MARC::Record &record,
    std::unordered_map<std::string, std::set<std::string>> * const stemmed_keyword_to_stemmed_keyphrases_map,
    std::unordered_map<std::string, std::string> * const stemmed_keyphrases_to_unstemmed_keyphrases_map)
{
    const std::string language_code(MARC::GetLanguageCode(record));
    const Stemmer * const stemmer(language_code.empty() ? nullptr : Stemmer::StemmerFactory(language_code));

    size_t extracted_count(ExtractKeywordsFromKeywordChainFields(record, stemmer,
                                                                 stemmed_keyword_to_stemmed_keyphrases_map,
                                                                 stemmed_keyphrases_to_unstemmed_keyphrases_map));
    return extracted_count;
}


void ExtractStemmedKeywords(
    MARC::Reader * const marc_reader,
    std::unordered_map<std::string, std::set<std::string>> * const stemmed_keyword_to_stemmed_keyphrases_map,
    std::unordered_map<std::string, std::string> * const stemmed_keyphrases_to_unstemmed_keyphrases_map)
{
    LOG_INFO("Starting extraction and stemming of pre-existing keywords.");

    unsigned total_count(0), records_with_keywords_count(0), keywords_count(0);
    while (const MARC::Record record = marc_reader->read()) {
        ++total_count;

        const size_t extracted_count(
            ExtractAllKeywords(record, stemmed_keyword_to_stemmed_keyphrases_map,
                               stemmed_keyphrases_to_unstemmed_keyphrases_map));
        if (extracted_count > 0) {
            ++records_with_keywords_count;
            keywords_count += extracted_count;
        }
    }

    LOG_INFO(std::to_string(total_count) + " records processed.");
    LOG_INFO(std::to_string(records_with_keywords_count) + " records had keywords.");
    LOG_INFO(std::to_string(keywords_count) + " keywords were extracted of which " +
             std::to_string(stemmed_keyword_to_stemmed_keyphrases_map->size()) + " were unique.");
}


// Checks to see if "value" is in any of the sets in "key_to_set_map".
bool ContainedInMapValues(const std::string &value,
                          const std::unordered_map<std::string, std::set<std::string>> &key_to_set_map)
{
    for (const auto &key_and_set : key_to_set_map) {
        for (const auto &set_entry : key_and_set.second) {
            if (set_entry == value)
                return true;
        }
    }

    return false;
}


// The following constant is used to reject cases where a key phrase consists of exactly one word and
// that single word is not as least as long as the constant.  This is used to try to increase precision
// but, of course, decreases recall.  Part of the reason why this seems necessary is the crappy stemmer.
constexpr auto MIN_SINGLE_STEMMED_KEYWORD_LENGTH(7);


void AugmentRecordsWithTitleKeywords(
    MARC::Reader * const marc_reader, MARC::Writer * const marc_writer,
    const std::unordered_map<std::string, std::set<std::string>> &stemmed_keyword_to_stemmed_keyphrases_map,
    const std::unordered_map<std::string, std::string> &stemmed_keyphrases_to_unstemmed_keyphrases_map,
    const std::map<std::string, std::unordered_set<std::string>> &language_codes_to_stopword_sets)
{
    LOG_INFO("Starting augmentation of stopwords.");

    unsigned total_count(0), augmented_record_count(0);
    while (MARC::Record record = marc_reader->read()) {
        ++total_count;

        // Look for a title...
        const auto title_field(record.findTag("245"));
        if (title_field == record.end()) {
            marc_writer->write(record);
            continue;
        }

        // ...in subfields 'a', 'b', 'c' and 'p':
        const auto subfields(title_field->getSubfields());
        if (not subfields.hasSubfield('a')) {
            marc_writer->write(record);
            continue;
        }

        std::string title;
        for (const char subfield_code : "abp") {
            const auto value(subfields.getFirstSubfieldWithCode(subfield_code));
            if (not value.empty())
                title += " " + value;
        }
        assert(not title.empty());

        std::string lowercase_title;
        TextUtil::UTF8ToLower(title, &lowercase_title);
        std::vector<std::string> title_words;
        TextUtil::ChopIntoWords(lowercase_title, &title_words, MIN_WORD_LENGTH);

        // Remove language-appropriate stop words from the title words:
        const std::string language_code(MARC::GetLanguageCode(record));
        const auto code_and_stopwords(language_codes_to_stopword_sets.find(language_code));
        if (code_and_stopwords != language_codes_to_stopword_sets.end())
            FilterOutStopwords(code_and_stopwords->second, &title_words);
        if (language_code != "eng") // Hack because people suck at cataloging!
            FilterOutStopwords(language_codes_to_stopword_sets.find("eng")->second, &title_words);

        if (title_words.empty()) {
            marc_writer->write(record);
            continue;
        }

        // If we have an appropriate stemmer, replace the title words w/ stemmed title words:
        const Stemmer * const stemmer(language_code.empty() ? nullptr : Stemmer::StemmerFactory(language_code));
        if (stemmer != nullptr) {
            std::vector<std::string> stemmed_title_words;
            for (const auto &title_word : title_words)
                stemmed_title_words.emplace_back(stemmer->stem(title_word));
            title_words.swap(stemmed_title_words);
        }

        std::unordered_map<std::string, std::set<std::string>> local_stemmed_keyword_to_stemmed_keyphrases_map;
        std::unordered_map<std::string, std::string> local_stemmed_keyphrases_to_unstemmed_keyphrases_map;
        ExtractAllKeywords(record, &local_stemmed_keyword_to_stemmed_keyphrases_map,
                           &local_stemmed_keyphrases_to_unstemmed_keyphrases_map);

        // Find title phrases that match stemmed keyphrases:
        std::unordered_set<std::string> new_keyphrases;
        for (const auto &title_word : title_words) {
            const auto word_and_set(stemmed_keyword_to_stemmed_keyphrases_map.find(title_word));
            if (word_and_set == stemmed_keyword_to_stemmed_keyphrases_map.end())
                continue;

            for (const std::string &stemmed_phrase : word_and_set->second) {
                if (ContainedInMapValues(stemmed_phrase, local_stemmed_keyword_to_stemmed_keyphrases_map))
                    continue; // We already have this in our MARC record.

                std::vector<std::string> stemmed_phrase_as_vector;
                StringUtil::Split(stemmed_phrase, ' ', &stemmed_phrase_as_vector, /* suppress_empty_components = */true);
                if (stemmed_phrase_as_vector.size() == 1
                    and stemmed_phrase_as_vector[0].length() < MIN_SINGLE_STEMMED_KEYWORD_LENGTH)
                    continue;

                if (TextUtil::FindSubstring(title_words, stemmed_phrase_as_vector) != title_words.end()) {
                    const auto stemmed_and_unstemmed_keyphrase(
                        stemmed_keyphrases_to_unstemmed_keyphrases_map.find(stemmed_phrase));
                    new_keyphrases.insert(stemmed_and_unstemmed_keyphrase->second);
                }
            }
        }

        if (new_keyphrases.empty()) {
            marc_writer->write(record);
            continue;
        }

        // Augment the record with new keywords derived from title words:
        for (const auto &new_keyword : new_keyphrases)
            record.insertField("601", { { 'a', new_keyword } });

        marc_writer->write(record);
        ++augmented_record_count;
    }

    LOG_INFO(std::to_string(augmented_record_count) + " records of " + std::to_string(total_count) +
             " were augmented w/ additional keywords.");
}


} // unnamed namespace


int Main(int argc, char **argv) {
    if (argc < 3)
        Usage();

    const std::string marc_input_filename(argv[1]);
    const std::string marc_output_filename(argv[2]);
    if (unlikely(marc_input_filename == marc_output_filename))
        LOG_ERROR("MARC input file name equals MARC output file name!");

    std::unique_ptr<MARC::Reader> marc_reader(MARC::Reader::Factory(marc_input_filename, MARC::FileType::BINARY));
    std::unique_ptr<MARC::Writer> marc_writer(MARC::Writer::Factory(marc_output_filename, MARC::FileType::BINARY));

    // Read optional stopword lists:
    std::map<std::string, std::unordered_set<std::string>> language_codes_to_stopword_sets;
    for (int arg_no(3); arg_no < argc; ++arg_no) {
        RegexMatcher * const matcher(RegexMatcher::RegexMatcherFactory("stopwords\\....$"));
        const std::string stopwords_filename(argv[arg_no]);
        std::string err_msg;
        if (not matcher->matched(stopwords_filename, &err_msg))
            LOG_ERROR("Invalid stopwords filename \"" + stopwords_filename + "\"!");
        const std::string language_code(stopwords_filename.substr(stopwords_filename.length() - 3));
        File stopwords(stopwords_filename, "r");
        if (not stopwords)
            LOG_ERROR("can't open \"" + stopwords_filename + "\" for reading!");
        std::unordered_set<std::string> stopwords_set;
        LoadStopwords(&stopwords, language_code, &stopwords_set);
        language_codes_to_stopword_sets[language_code] = stopwords_set;
    }

    // We always need English because librarians suck at specifying English:
    if (language_codes_to_stopword_sets.find("eng") == language_codes_to_stopword_sets.end())
        LOG_ERROR("You always need to provide \"stopwords.eng\"!");

    std::unordered_map<std::string, std::set<std::string>> stemmed_keyword_to_stemmed_keyphrases_map;
    std::unordered_map<std::string, std::string> stemmed_keyphrases_to_unstemmed_keyphrases_map;
    ExtractStemmedKeywords(marc_reader.get(), &stemmed_keyword_to_stemmed_keyphrases_map,
                            &stemmed_keyphrases_to_unstemmed_keyphrases_map);
    marc_reader->rewind();
    AugmentRecordsWithTitleKeywords(marc_reader.get(), marc_writer.get(),
                                    stemmed_keyword_to_stemmed_keyphrases_map,
                                    stemmed_keyphrases_to_unstemmed_keyphrases_map,
                                    language_codes_to_stopword_sets);

    return EXIT_SUCCESS;
}
