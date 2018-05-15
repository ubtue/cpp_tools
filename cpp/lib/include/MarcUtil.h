/** \file   MarcUtil.h
 *  \brief  Various utility functions related to the processing of MARC-21 records.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *  \author Oliver Obenland (oliver.obenland@uni-tuebingen.de)
 *
 *  \copyright 2014-2017 Universitätsbibliothek Tübingen.  All rights reserved.
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


#include <unordered_map>
#include "MarcRecord.h"


// Forward declarations:
class MarcReader;
class MarcWriter;


namespace MarcUtil {


/** \brief True if a GND code was found in 035$a else false. */
bool GetGNDCode(const MarcRecord &record, std::string *const gnd_code);


bool UBTueIsElectronicResource(const MarcRecord &marc_record);


/** \return A Non-empty string if we managed to find a parent PPN o/w the empty string. */
std::string GetParentPPN(const MarcRecord &marc_record);


/** \brief Populates a map of control numbers to record offsets.
 *  \return The number of processed records.
 */
unsigned CollectRecordOffsets(MarcReader * const marc_reader,
                              std::unordered_map<std::string, off_t> * const control_number_to_offset_map);


bool IsArticle(const MarcRecord &marc_record);


bool HasSubfieldWithValue(const MarcRecord &marc_record, const std::string &tag, const char subfield_code,
                          const std::string &value);


/** \true if the record has at lest one field with tag "tag" and that field has a subfield with subfield code
 *        "subfield_code".
 */
bool HasTagAndSubfield(const MarcRecord &marc_record, const std::string &tag, const char subfield_code);


void FileLockedComposeAndWriteRecord(MarcWriter * const marc_writer, MarcRecord * const record);


} // namespace MarcUtil
