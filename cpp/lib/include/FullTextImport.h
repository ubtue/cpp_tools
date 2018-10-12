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
    std::string normalised_title_;
    std::set<std::string> normalised_authors_;
    std::vector<std::string> full_text_;
};


// Writes full-text data as a text file to disk. The full-text is expected to delimited into chunks at the bare minimum.
// Format:
// Line 1: <normalized_title>
// Line 2: <normalized authors>
// Line 3...: <full_text>
void WriteExtractedTextToDisk(const std::string &full_text, const std::string &normalised_title,
                              const std::set<std::string> &normalised_authors, File * const output_file);


// Reads in and parses a text file previously written to disk with WriteExtractedTextToDisk() into a FullTextData instance.
void ReadExtractedTextFromDisk(File * const input_file, FullTextData * const full_text_data);


} // namespace FullTextImport
