/** \file   BSZUtil.h
 *  \brief  Various utility functions related to data etc. having to do w/ the BSZ.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *  \author Oliver Obenland (oliver.obenland@uni-tuebingen.de)
 *
 *  \copyright 2017 Universitätsbibliothek Tübingen.  All rights reserved.
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


#include <string>
#include <unordered_set>
#include "File.h"


namespace BSZUtil {


extern const size_t PPN_LENGTH_OLD;
extern const size_t PPN_LENGTH_NEW;


// Extracts PPNs (ID's) from a LOEPPN file as provided by the BSZ.
void ExtractDeletionIds(File * const deletion_list, std::unordered_set <std::string> * const delete_full_record_ids,
                        std::unordered_set <std::string> * const local_deletion_ids);


/** Extracts a date in the form of YYMMDD from "filename". */
std::string ExtractDateFromFilenameOrDie(const std::string &filename);


} // namespace BSZUtil
