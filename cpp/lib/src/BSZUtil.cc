/** \file   BSZUtil.h
 *  \brief  Various utility functions related to data etc. having to do w/ the BSZ.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *  \author Oliver Obenland (oliver.obenland@uni-tuebingen.de)
 *
 *  \copyright 2017,2018 Universitätsbibliothek Tübingen.  All rights reserved.
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

#include "BSZUtil.h"
#include "StringUtil.h"
#include "util.h"
#include "RegexMatcher.h"


namespace BSZUtil {


// Use the following indicators to select whether to fully delete a record or remove its local data
// For a description of indicators
// c.f. https://wiki.bsz-bw.de/doku.php?id=v-team:daten:datendienste:sekkor (20160426)
const char FULL_RECORD_DELETE_INDICATORS[] = { 'A', 'B', 'C', 'D', 'E' };
const char LOCAL_DATA_DELETE_INDICATORS[] = { '3', '4', '5', '9' };

/*
 * The PPN length was increased from 9 to 10 in 2018.
 * The 10th character can optionally be a space
 */
const size_t MAX_LINE_LENGTH_OLD_WITH_ILN(25);
const size_t MAX_LINE_LENGTH_OLD_NO_ILN(21);
const size_t MAX_LINE_LENGTH_NEW_WITH_ILN(26);
const size_t MAX_LINE_LENGTH_NEW_NO_ILN(22);

const size_t PPN_LENGTH_OLD(9);
const size_t PPN_LENGTH_NEW(10);
const size_t PPN_START_INDEX(12);
const size_t SEPARATOR_INDEX(PPN_START_INDEX - 1);


void ExtractDeletionIds(File * const deletion_list, std::unordered_set <std::string> * const delete_full_record_ids,
                        std::unordered_set <std::string> * const local_deletion_ids)
{
    unsigned line_no(0);
top_loop:
    while (not deletion_list->eof()) {
        const std::string line(StringUtil::Trim(deletion_list->getline()));
        ++line_no;
        if (unlikely(line.empty())) // Ignore empty lines.
            continue;

        const size_t line_len(line.length());
        size_t ppn_len(0);

        if (line_len == MAX_LINE_LENGTH_OLD_WITH_ILN or line_len == MAX_LINE_LENGTH_OLD_NO_ILN)
            ppn_len = PPN_LENGTH_OLD;
        else if (line_len == MAX_LINE_LENGTH_NEW_WITH_ILN or line_len == MAX_LINE_LENGTH_NEW_NO_ILN)
            ppn_len = PPN_LENGTH_NEW;
        else {
            LOG_ERROR("unexpected line length " + std::to_string(line_len)
                       + " for entry on line " + std::to_string(line_no)
                       + " in deletion list file \"" + deletion_list->getPath() + "\"!");
            ppn_len = PPN_LENGTH_OLD;       // fallback to the more conservative of the two lengths
        }

        for (const char indicator : FULL_RECORD_DELETE_INDICATORS) {
            if (line[SEPARATOR_INDEX] == indicator) {
                delete_full_record_ids->insert(StringUtil::Trim(line.substr(PPN_START_INDEX, ppn_len)));
                goto top_loop;
            }
        }
        for (const char indicator : LOCAL_DATA_DELETE_INDICATORS) {
            if (line[SEPARATOR_INDEX] == indicator) {
                local_deletion_ids->insert(StringUtil::Trim(line.substr(PPN_START_INDEX, ppn_len)));
                goto top_loop;
            }
        }
        LOG_WARNING("in \"" + deletion_list->getPath() + " \" on line #" + std::to_string(line_no)
                   + " unknown indicator: '" + line.substr(SEPARATOR_INDEX, 1) + "'!");
    }
}


std::string ExtractDateFromFilenameOrDie(const std::string &filename) {
    static const std::string DATE_EXTRACTION_REGEX("(\\d\\d[01]\\d[0123]\\d)");
    static RegexMatcher *matcher;
    if (matcher == nullptr) {
        std::string err_msg;
        matcher = RegexMatcher::RegexMatcherFactory(DATE_EXTRACTION_REGEX, &err_msg);
        if (unlikely(not err_msg.empty()))
            LOG_ERROR("in ExtractDateFromFilenameOrDie: failed to compile regex: \"" + DATE_EXTRACTION_REGEX
                     + "\".");
    }

    if (unlikely(not matcher->matched(filename)))
        LOG_ERROR("in ExtractDateFromFilenameOrDie: \"" + filename + "\" failed to match the regex \""
                 + DATE_EXTRACTION_REGEX + "\"!");

    return (*matcher)[1];
}


} // namespace BSZUtil
