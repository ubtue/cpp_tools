/** \file   VuFind.h
 *  \brief  VuFind-related constants and utility functions.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2015,2017,2019 Universitätsbibliothek Tübingen.  All rights reserved.
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


namespace VuFind {


/**
 * \return path to database config file in local_overrides directory.
 */
std::string GetDefaultDatabaseConf();


/** \brief Extracts the MySQL connection URL from a VuFind config file.
 *  \param vufind_config_file_path  If not specified, $VUFIND_HOME + "/" + VuFind::DATABASE_CONF will be used.
 *  \return The extracted URL
 */
std::string GetMysqlURL(const std::string &vufind_config_file_path = "");


/** \brief Get TueFind Flavour from ENV variable or empty string if not set. */
const std::string GetTueFindFlavour();


} // namespace VuFind
