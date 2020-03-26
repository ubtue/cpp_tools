/** \brief Classes related to the Zotero Harvester's interoperation with the Zeder database
 *  \author Madeeswaran Kannan
 *
 *  \copyright 2020 Universitätsbibliothek Tübingen.  All rights reserved.
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

#include "ZoteroHarvesterZederInterop.h"
#include <cmath>
#include "util.h"


namespace ZoteroHarvester {


namespace ZederInterop {


const std::map<Config::JournalParams::IniKey, std::string> INI_KEY_TO_ZEDER_COLUMN_MAP {
    { Config::JournalParams::IniKey::NAME,               "tit"  },
    { Config::JournalParams::IniKey::ONLINE_PPN,         "eppn" },
    { Config::JournalParams::IniKey::PRINT_PPN,          "pppn" },
    { Config::JournalParams::IniKey::ONLINE_ISSN,        "essn" },
    { Config::JournalParams::IniKey::PRINT_ISSN,         "issn" },
    { Config::JournalParams::IniKey::EXPECTED_LANGUAGES, "spr"  },
    { Config::JournalParams::IniKey::SSGN,               "ber"  },
//  The following two columns/INI keys are intentionally excluded as they are special cases.
//  Even though there is a one-to-one correspondence for each to the two columns,
//  they are stored differently in memory (in the Zeder::Entry class) than all other
//  columns. Therefore, they can't be trivially mapped to each other.
//  { Config::JournalParams::IniKey::ZEDER_ID, "Z" },
//  { Config::JournalParams::IniKey::ZEDER_MODIFIED_TIME, "Mtime" },
};


static std::string ResolveGroup(const Zeder::Entry &/*unused*/, const Zeder::Flavour zeder_flavour) {
    return Zeder::FLAVOUR_TO_STRING_MAP.at(zeder_flavour);
}


static std::string ResolveEntryPointURL(const Zeder::Entry &zeder_entry, const Zeder::Flavour zeder_flavour) {
    const auto &rss(zeder_entry.getAttribute("rss", ""));
    const auto &p_zot2(zeder_entry.getAttribute("p_zot2", ""));
    const auto &url1(zeder_entry.getAttribute("url1", ""));
    const auto &url2(zeder_entry.getAttribute("url2", ""));

    // Field priorities differ between IxTheo and KrimDok (based on who updated which field first)
    switch (zeder_flavour) {
    case Zeder::Flavour::IXTHEO:
        if (not rss.empty())
            return rss;
        else if (not p_zot2.empty())
            return p_zot2;
        else if (not url2.empty())
            return url2;
        else
            return url1;
    case Zeder::Flavour::KRIMDOK:
        if (not rss.empty())
            return rss;
        else if (not url2.empty())
            return url2;
        else if (not p_zot2.empty())
            return p_zot2;
        else
            return url1;
    default:
        return "";
    }
}


static std::string ResolveHarvesterOperation(const Zeder::Entry &zeder_entry, const Zeder::Flavour /*unused*/) {
    const auto &rss(zeder_entry.getAttribute("rss", ""));
    if (not rss.empty())
        return Config::HARVESTER_OPERATION_TO_STRING_MAP.at(Config::HarvesterOperation::RSS);
    else
        return Config::HARVESTER_OPERATION_TO_STRING_MAP.at(Config::HarvesterOperation::CRAWL);
}


static std::string ResolveUploadOperation(const Zeder::Entry &zeder_entry, const Zeder::Flavour /*unused*/) {
    const auto &prodf(zeder_entry.getAttribute("prodf", ""));
    if (prodf == "zotat")
        return Config::UPLOAD_OPERATION_TO_STRING_MAP.at(Config::UploadOperation::TEST);
    else if (prodf == "zota")
        return Config::UPLOAD_OPERATION_TO_STRING_MAP.at(Config::UploadOperation::LIVE);
    else
        return Config::UPLOAD_OPERATION_TO_STRING_MAP.at(Config::UploadOperation::NONE);
}


static std::string ResolveUpdateWindow(const Zeder::Entry &zeder_entry, const Zeder::Flavour /*unused*/) {
    // Calculate an admissible range in days for a frequency given per year.
    // Right now we simply ignore entries that cannot be suitably converted to float.
    float frequency_as_float;
    if (not StringUtil::ToFloat(zeder_entry.getAttribute("freq", ""), &frequency_as_float))
        return "";
    float admissible_range = (365 / frequency_as_float) * 1.5;
    return std::to_string(static_cast<int>(std::round(admissible_range)));
}


const std::map<Config::JournalParams::IniKey, std::function<std::string(const Zeder::Entry &, const Zeder::Flavour)>> INI_KEY_TO_ZEDER_RESOLVER_MAP {
    { Config::JournalParams::IniKey::GROUP, ResolveGroup },
    { Config::JournalParams::IniKey::ENTRY_POINT_URL, ResolveEntryPointURL },
    { Config::JournalParams::IniKey::HARVESTER_OPERATION, ResolveHarvesterOperation },
    { Config::JournalParams::IniKey::UPLOAD_OPERATION, ResolveUploadOperation },
    { Config::JournalParams::IniKey::UPDATE_WINDOW, ResolveUpdateWindow }
};


static inline bool IsValidZederValue(const std::string &zeder_value) {
    return zeder_value != "NV";
}


std::string GetJournalParamsIniValueFromZederEntry(const Zeder::Entry &zeder_entry, const Zeder::Flavour zeder_flavour,
                                                   const Config::JournalParams::IniKey ini_key)
{
    std::string zeder_value;
    if (INI_KEY_TO_ZEDER_COLUMN_MAP.find(ini_key) != INI_KEY_TO_ZEDER_COLUMN_MAP.end())
        zeder_value = zeder_entry.getAttribute(INI_KEY_TO_ZEDER_COLUMN_MAP.at(ini_key), "");
    else if (INI_KEY_TO_ZEDER_RESOLVER_MAP.find(ini_key) != INI_KEY_TO_ZEDER_RESOLVER_MAP.end())
        zeder_value = INI_KEY_TO_ZEDER_RESOLVER_MAP.at(ini_key)(zeder_entry, zeder_flavour);
    else
        LOG_ERROR("unable to resolve value from Zeder entry for INI key '" + Config::JournalParams::GetIniKeyString(ini_key) + "'");

    zeder_value = TextUtil::CollapseAndTrimWhitespace(zeder_value);

    if (IsValidZederValue(zeder_value))
        return zeder_value;
    else
        return "";
}


Zeder::Flavour GetZederInstanceForJournal(const Config::JournalParams &journal_params) {
    if (journal_params.group_ == "IxTheo" or journal_params.group_ == "ixtheo")
        return Zeder::Flavour::IXTHEO;
    else if (journal_params.group_ == "RelBib" or journal_params.group_ == "relbib")
        return Zeder::Flavour::IXTHEO;
    else if (journal_params.group_ == "KrimDok" or journal_params.group_ == "krimdok")
        return Zeder::Flavour::KRIMDOK;

    LOG_ERROR("unknown group '" + journal_params.group_ + "' for journal '" + journal_params.name_ + "'");
}


Zeder::Flavour GetZederInstanceFromMarcRecord(const MARC::Record &record) {
    for (const auto &field : record.getTagRange("935")) {
        const auto sigil(field.getFirstSubfieldWithCode('a'));
        if (sigil == "mteo")
            return Zeder::Flavour::IXTHEO;
        else if (sigil == "mkri")
            return Zeder::Flavour::KRIMDOK;
    }

    throw std::runtime_error("missing sigil field in Zotero record '" + record.getControlNumber() + "'");
}


} // end namespace ZederInterop


} // end namespace ZoteroHarvester
