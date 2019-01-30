/** \file    NGram.cc
 *  \brief   Implementation of ngram related utility functions.
 *  \author  Dr. Johannes Ruscheinski
 */

/*
 *  Copyright 2003-2009 Project iVia.
 *  Copyright 2003-2009 The Regents of The University of California.
 *  Copyright 2019 Universitätsbibliothek Tübingen.
 *
 *  This file is part of the libiViaCore package.
 *
 *  The libiViaCore package is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU Lesser General Public License as published
 *  by the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  libiViaCore is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  You should have received a copy of the GNU Lesser General Public License
 *  along with libiViaCore; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
#include "NGram.h"
#include <algorithm>
#include <fstream>
#include <numeric>
#include <unordered_map>
#include <unordered_set>
#include <climits>
#include <cmath>
#include "BinaryIO.h"
#include "FileUtil.h"
#include "TextUtil.h"
#include "UBTools.h"
#include "util.h"


namespace {


void Split(const std::wstring &s, std::vector<std::wstring> * const words) {
    bool in_word(false);
    std::wstring new_word;
    for (const auto ch : s) {
        if (std::iswspace(ch)) {
            if (in_word) {
                words->push_back(new_word);
                in_word = false;
            }
        } else if (in_word)
            new_word += ch;
        else {
            in_word = true;
            new_word = ch;
        }
    }

    if (in_word)
        words->push_back(new_word);
}


static std::string GetLoadLanguageModelDirectory(const std::string &override_language_models_directory) {
    return override_language_models_directory.empty() ? UBTools::GetTuelibPath() + "/language_models"
                                                      : override_language_models_directory;
}


// LoadLanguageModels -- returns true if at least one language model was loaded
//                       from "language_models_directory"
//
bool LoadLanguageModels(std::vector<NGram::LanguageModel> * const language_models, const std::string &override_language_models_directory) {
    FileUtil::Directory directory(GetLoadLanguageModelDirectory(override_language_models_directory), ".+\\.lm");
    bool found_at_least_one_language_model(false);
    for (const auto &dir_entry : directory) {
        const std::string language(dir_entry.getName().substr(0, dir_entry.getName().length() - 3 /* strip off ".lm" */));
        NGram::LanguageModel language_model;
        NGram::LoadLanguageModel(language, &language_model, override_language_models_directory);
        language_models->push_back(language_model);
        found_at_least_one_language_model = true;
    }

    return found_at_least_one_language_model;
}


// Filters out anything except for letters and space characters and converts UTF8 to wide characters.
std::wstring PreprocessText(const std::string &utf8_string) {
    std::wstring wchar_string;
    if (unlikely(not TextUtil::UTF8ToWCharString(utf8_string, &wchar_string)))
        LOG_ERROR("failed to convert UTF* to wide characters!");

    std::wstring filtered_string;
    filtered_string.reserve(wchar_string.size());
    for (const auto ch : wchar_string) {
        if (std::iswalpha(ch) or std::iswspace(ch))
            filtered_string += ch;
    }

    return filtered_string;
}


} // unnamed namespace


namespace NGram {


UnitVector::UnitVector(const NGramCounts &ngram_counts): std::vector<std::pair<std::wstring, double>>(ngram_counts) {
    double norm_squared(0.0);
    for (const auto &ngram_and_weight : *this)
        norm_squared += ngram_and_weight.second;

    if (norm_squared != 0.0) {
        const double norm(std::sqrt(norm_squared));
        for (auto &ngram_and_weight : *this)
            ngram_and_weight.second /= norm;
    }

    if (logger->getMinimumLogLevel() == Logger::LL_DEBUG) {
        double norm_squared2(0.0);
        for (auto &ngram_and_weight : *this)
            norm_squared2 += ngram_and_weight.second;
        LOG_DEBUG("norm  sqared is " + std::to_string(std::sqrt(norm_squared2)));
    }
}


double UnitVector::dotProduct(const UnitVector &rhs) const {
    std::unordered_map<std::wstring, double> rhs_map;
    for (const auto &rhs_ngram_and_weight : rhs)
        rhs_map.emplace(rhs_ngram_and_weight);

    double dot_product(0.0);
    for (const auto &ngram_and_weight : *this) {
        const auto rhs_ngram_and_weight(rhs_map.find(ngram_and_weight.first));
        if (rhs_ngram_and_weight != rhs_map.cend())
            dot_product += ngram_and_weight.second * rhs_ngram_and_weight->second;
    }

    return dot_product;
}


void UnitVector::prettyPrint(std::ostream &output) const {
    output << "#entries = " << size() << '\n';
    for (const auto &ngram_and_core : *this)
        output << '\'' << TextUtil::WCharToUTF8StringOrDie(ngram_and_core.first) << "' = " << ngram_and_core.second << '\n';
    output << '\n';
}


// LoadLanguageModel -- loads a language model from "path_name" into "language_model".
//
void LoadLanguageModel(const std::string &language, LanguageModel * const language_model,
                       const std::string &override_language_models_directory)
{
    const std::string model_path(GetLoadLanguageModelDirectory(override_language_models_directory) + "/" + language + ".lm");
    const auto input(FileUtil::OpenInputFileOrDie(model_path));
    if (input->fail())
        LOG_ERROR("can't open language model file \"" + model_path + "\" for reading!");

    size_t entry_count;
    BinaryIO::ReadOrDie(*input, &entry_count);
    NGramCounts ngram_counts;
    ngram_counts.reserve(entry_count);

    for (unsigned i(0); i < entry_count; ++i) {
        std::wstring ngram;
        BinaryIO::ReadOrDie(*input, &ngram);

        double score;
        BinaryIO::ReadOrDie(*input, &score);

        ngram_counts.emplace_back(ngram, score);
    }

    *language_model = LanguageModel(language, ngram_counts);
}


void CreateLanguageModel(std::istream &input, LanguageModel * const language_model, const unsigned ngram_number_threshold,
                         const unsigned topmost_use_count)
{
    const std::string file_contents(std::istreambuf_iterator<char>(input), {});
    const std::wstring filtered_text(PreprocessText(file_contents));

    std::vector<std::wstring> words;
    Split(filtered_text, &words);

    std::unordered_map<std::wstring, double> ngram_counts_map;
    unsigned total_ngram_count(0);
    for (std::vector<std::wstring>::const_iterator word(words.begin()); word != words.end(); ++word) {
        const std::wstring funny_word(L"_" + *word + L"_");
        const std::wstring::size_type funny_word_length(funny_word.length());
        std::wstring::size_type length(funny_word_length);
        for (unsigned i = 0; i < funny_word_length; ++i, --length) {
            if (length > 4) {
                const std::wstring ngram(funny_word.substr(i, 5));
                auto ngram_count(ngram_counts_map.find(ngram));
                if (ngram_count == ngram_counts_map.end())
                    ngram_counts_map[ngram] = 1.0;
                else
                    ++ngram_counts_map[ngram];
                ++total_ngram_count;
            }

            if (length > 3) {
                const std::wstring ngram(funny_word.substr(i, 4));
                auto ngram_count(ngram_counts_map.find(ngram));
                if (ngram_count == ngram_counts_map.end())
                    ngram_counts_map[ngram] = 1.0;
                else
                    ++ngram_counts_map[ngram];
                ++total_ngram_count;
            }

            if (length > 2) {
                const std::wstring ngram(funny_word.substr(i, 3));
                auto ngram_count(ngram_counts_map.find(ngram));
                if (ngram_count == ngram_counts_map.end())
                    ngram_counts_map[ngram] = 1.0;
                else
                    ++ngram_counts_map[ngram];
                ++total_ngram_count;
            }

            if (length > 1) {
                const std::wstring ngram(funny_word.substr(i, 2));
                auto ngram_count(ngram_counts_map.find(ngram));
                if (ngram_count == ngram_counts_map.end())
                    ngram_counts_map[ngram] = 1.0;
                else
                    ++ngram_counts_map[ngram];
                ++total_ngram_count;
            }

            const std::wstring ngram(funny_word.substr(i, 1));
            auto ngram_count(ngram_counts_map.find(ngram));
            if (ngram_count == ngram_counts_map.end())
                ngram_counts_map[ngram] = 1.0;
            else
                ++ngram_counts_map[ngram];
            ++total_ngram_count;
        }
    }

    if (unlikely(ngram_counts_map.size() < topmost_use_count))
        LOG_ERROR("generated too few ngrams (< " + std::to_string(topmost_use_count) + ")!");

    NGramCounts ngram_counts_vector;
    ngram_counts_vector.reserve(ngram_counts_map.size());
    for (const auto &ngram_and_count : ngram_counts_map)
        ngram_counts_vector.emplace_back(ngram_and_count);

    std::sort(ngram_counts_vector.begin(), ngram_counts_vector.end(),
              [](const std::pair<std::wstring, double> &a, const std::pair<std::wstring, double> &b){ return a.second > b.second; });

    // Eliminate all entries that have a count < ngram_number_threshold:
    auto iter(ngram_counts_vector.rbegin());
    for (/* Intentionally empty! */; iter != ngram_counts_vector.rend(); ++iter) {
        if (iter->second > ngram_number_threshold)
            break;
    }
    ngram_counts_vector.resize(ngram_counts_vector.rend() - iter);

    if (ngram_counts_vector.size() >= topmost_use_count)
        ngram_counts_vector.resize(topmost_use_count);

    *language_model = LanguageModel("unknown", ngram_counts_vector);
}


void ClassifyLanguage(std::istream &input, std::vector<std::string> * const top_languages, const std::set<std::string> &considered_languages,
                      const unsigned ngram_number_threshold, const unsigned topmost_use_count, const double alternative_cutoff_factor,
                      const std::string &override_language_models_directory)
{
    LanguageModel unknown_language_model;
    CreateLanguageModel(input, &unknown_language_model, ngram_number_threshold, topmost_use_count);

    static bool models_already_loaded(false);
    static std::vector<LanguageModel> language_models;
    if (not models_already_loaded) {
        models_already_loaded = true;
        if (not LoadLanguageModels(&language_models, override_language_models_directory))
            LOG_ERROR("no language models available in \"" + GetLoadLanguageModelDirectory(override_language_models_directory) + "\"!");
        LOG_DEBUG("loaded " + std::to_string(language_models.size()) + " language models.");
    }

    // Verify that we do have models for all requested languages:
    if (not considered_languages.empty()) {
        std::unordered_set<std::string> all_languages;
        for (const auto &language_model : language_models)
            all_languages.emplace(language_model.getLanguage());

        for (const auto &requested_language : considered_languages) {
            if (unlikely(all_languages.find(requested_language) == all_languages.cend()))
                LOG_ERROR("considered language \"" + requested_language + "\" is not supported!");
        }
    }

    std::vector<std::pair<std::string, double>> languages_and_scores;
    for (const auto &language_model : language_models) {
        if (not considered_languages.empty() and considered_languages.find(language_model.getLanguage()) == considered_languages.cend())
            continue;

        const double similarity(language_model.similarity(unknown_language_model));
        languages_and_scores.emplace_back(language_model.getLanguage(), similarity);
        LOG_DEBUG(language_model.getLanguage() + " scored + " + std::to_string(similarity));
    }
    std::sort(languages_and_scores.begin(), languages_and_scores.end(),
              [](const std::pair<std::string, double> &a, const std::pair<std::string, double> &b){ return a.second < b.second; });

    // Select the top scoring language and anything that's close (as defined by alternative_cutoff_factor):
    const double high_score(languages_and_scores[0].second);
    top_languages->push_back(languages_and_scores[0].first);
    for (unsigned i(1); i < languages_and_scores.size() and (languages_and_scores[i].second < alternative_cutoff_factor * high_score); ++i)
        top_languages->push_back(languages_and_scores[i].first);
}


void CreateAndWriteLanguageModel(std::istream &input, const std::string &output_path, const unsigned ngram_number_threshold,
                                 const unsigned topmost_use_count)
{
    LanguageModel language_model;
    CreateLanguageModel(input, &language_model, ngram_number_threshold, topmost_use_count);

    const auto output(FileUtil::OpenOutputFileOrDie(output_path));
    BinaryIO::WriteOrDie(*output, language_model.size());
    for (const auto &ngram_and_rank : language_model) {
        LOG_DEBUG("\"" + TextUtil::WCharToUTF8StringOrDie(ngram_and_rank.first) + "\" = " + std::to_string(ngram_and_rank.second));
        BinaryIO::WriteOrDie(*output, ngram_and_rank.first);
        BinaryIO::WriteOrDie(*output, ngram_and_rank.second);
    }
}


} // namespace NGram
