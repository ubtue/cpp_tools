/** \file    canon_law_to_codes_tool.cc
 *  \brief   A tool for converting canon law references to numeric codes.
 *  \author  Dr. Johannes Ruscheinski
 */

/*
    Copyright (C) 2019 Library of the University of Tübingen

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
#include <iostream>
#include <cstdlib>
#include "MiscUtil.h"
#include "StringUtil.h"
#include "util.h"


namespace {


} // unnamed namespace


int Main(int argc, char **argv) {
    if (argc != 2)
        ::Usage("canon_law_reference_candidate");;

    const std::string canon_law_reference_candidate(StringUtil::TrimWhite(argv[1]));
    std::string range;

    enum Codex { CIC1917, CIC1983, CCEO } codex;
    if (StringUtil::StartsWith(canon_law_reference_candidate, "CCEO", /* ignore_case = */true)) {
        codex = CCEO;
        range = StringUtil::TrimWhite(canon_law_reference_candidate.substr(__builtin_strlen("CCEO")));
    } else if (StringUtil::StartsWith(canon_law_reference_candidate, "CIC1917", /* ignore_case = */true)) {
        codex = CIC1917;
        range = StringUtil::TrimWhite(canon_law_reference_candidate.substr(__builtin_strlen("CIC1917")));
    } else if (StringUtil::StartsWith(canon_law_reference_candidate, "CIC1983", /* ignore_case = */true)) {
        codex = CIC1983;
        range = StringUtil::TrimWhite(canon_law_reference_candidate.substr(__builtin_strlen("CIC1983")));
    } else
        LOG_ERROR("can't determine codes!");

    unsigned range_start, range_end;
    if (range.empty()) {
        range_start = 0;
        range_end = 99999999;
    } else if (not MiscUtil::ParseCanonLawRanges(range, &range_start, &range_end))
        LOG_ERROR("don't know how to parse codex parts \"" + range + "\"!");

    switch (codex) {
    case CIC1917:
        std::cout << StringUtil::ToString(100000000 + range_start) << '_' << StringUtil::ToString(100000000 + range_end) << '\n';
    case CIC1983:
        std::cout << StringUtil::ToString(200000000 + range_start) << '_' << StringUtil::ToString(200000000 + range_end) << '\n';
    case CCEO:
        std::cout << StringUtil::ToString(300000000 + range_start) << '_' << StringUtil::ToString(300000000 + range_end) << '\n';
    }

    return EXIT_SUCCESS;
}
