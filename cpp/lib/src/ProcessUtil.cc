/** \file    ProcessUtil.c
 *  \brief   The ProcessUtil implementation.
 *  \author  Dr. Johannes Ruscheinski
 */

/*
 *  Copyright 2020 University Library of Tübingen
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
#include "ProcessUtil.h"
#include "FileUtil.h"
#include "StringUtil.h"


namespace ProcessUtil {


std::unordered_set<pid_t> GetProcessIdsForPath(const std::string &path) {
    std::unordered_set<pid_t> pids;

    FileUtil::Directory proc("/proc", "\\d+"); // Only PID's
    for (const auto &pid_dir : proc) {
        FileUtil::Directory fd_dir("/proc/" + pid_dir.getName() + "/fd");
        for (const auto &link : fd_dir) {
            std::string link_target;
            if (FileUtil::ReadLink("/proc/" + pid_dir.getName() + "/fd/" + link.getName(), &link_target) and link_target == path) {
                pids.emplace(StringUtil::ToNumber(FileUtil::GetBasename(pid_dir.getName())));
                break;
            }
        }
    }

    return pids;
}


} // namespace ProcessUtil
