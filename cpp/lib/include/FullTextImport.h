 /*
 *  \brief   Interface to upload metadata-augmented full-text to Elasticsearch
 *  \author  Madeeswaran Kannan
 *
 *  Copyright (C) 2018, Library of the University of Tübingen
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


#include <iostream>
#include <set>
#include <unordered_set>
#include <cctype>
#include <cstdlib>
#include "ControlNumberGuesser.h"
#include "Elasticsearch.h"
#include "MARC.h"
#include "StringUtil.h"
#include "util.h"


namespace FullTextImport {


extern const std::string CHUNK_DELIMITER;
extern const std::string PARAGRAPH_DELIMITER;


// Represents a full-text document that can potentially be correlated with a record on IxTheo
// The actual full-text consists of multiple chunks of arbitrary text sequences.
// What constitutes a chunk is dependent on the source of the full-text.
struct FullTextData {
    std::string title_;
    std::set<std::string> authors_;
    std::string year_;
    std::vector<std::string> full_text_;

    inline bool hasValidMetadata() const {
        return not title_.empty() and not authors_.empty() and not year_.empty();
    }
};


// Writes full-text data as a text file to disk. The full-text is expected to be split into chunks and formatted in the following manner:
// Line 1: <title>
// Line 2: <authors>
// Line 3: <year>
// Line 4: <full_text>
void WriteExtractedTextToDisk(const std::string &full_text, const std::string &title,
                              const std::set<std::string> &authors, const std::string &year, File * const output_file);


// Reads in and parses a text file previously written to disk with WriteExtractedTextToDisk() into a FullTextData instance.
void ReadExtractedTextFromDisk(File * const input_file, FullTextData * const full_text_data);


// Match full-text data with an existing record's control number, if any. Returns the number of exact matches.
size_t CorrelateFullTextData(const std::vector<std::shared_ptr<FullTextData>> &full_text_data,
                            std::unordered_map<std::string, std::shared_ptr<FullTextData>> * const control_number_to_full_text_data_map);


} // namespace FullTextImport
