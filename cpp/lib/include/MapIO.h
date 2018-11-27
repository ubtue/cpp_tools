/** \file   MapIO.h
 *  \brief  Map-IO-related utility functions.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2015,2018 Universitätsbibliothek Tübingen.  All rights reserved.
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


#include <fstream>
#include <string>
#include <unordered_map>


// Forward declaration:
class File;


namespace MapIO {


/** \brief Replaces slashes, equal-signs and semicolons with a slash followed by the respective character. */
std::string Escape(const std::string &s);

/** \brief Writes "map" to "output_filename" in a format that can be red in by DeserialiseMap(). */
void SerialiseMap(const std::string &output_filename, const std::unordered_map<std::string, std::string> &map);

/** \brief Reads "map: from "input_filename".  Aborts on input errors and emits an error message on stderr. */
void DeserialiseMap(const std::string &input_filename, std::unordered_map<std::string, std::string> * const map);

/** \brief Writes "multimap" to "output_filename" in a format that can be red in by DeserialiseMap(). */
void SerialiseMap(const std::string &output_filename, const std::unordered_multimap<std::string, std::string> &map);

/** \brief Reads "multimap" from "input_filename".  Aborts on input errors and emits an error message on stderr. */
void DeserialiseMap(const std::string &input_filename, std::unordered_multimap<std::string, std::string> * const multimap);

void WriteEntry(File * const map_file, const std::string &key, const std::string &value);


} // namespace MapIO
