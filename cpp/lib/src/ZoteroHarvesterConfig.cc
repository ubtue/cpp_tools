/** \brief Classes related to the Zotero Harvester's configuration data
 *  \author Madeeswaran Kannan
 *
 *  \copyright 2019 Universitätsbibliothek Tübingen.  All rights reserved.
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

#include "MapUtil.h"
#include "MARC.h"
#include "StringUtil.h"
#include "TranslationUtil.h"
#include "UBTools.h"
#include "ZoteroHarvesterConfig.h"
#include "util.h"


namespace ZoteroHarvester {


namespace Config {


const std::map<int, std::string> HARVESTER_OPERATION_TO_STRING_MAP{
    { HarvesterOperation::RSS,    "RSS"    },
    { HarvesterOperation::CRAWL,  "CRAWL"  },
    { HarvesterOperation::DIRECT, "DIRECT" }
};
const std::map<std::string, int> STRING_TO_HARVEST_OPERATION_MAP {
    { "RSS",    HarvesterOperation::RSS    },
    { "DIRECT", HarvesterOperation::DIRECT },
    { "CRAWL",  HarvesterOperation::CRAWL  }
};


const std::map<std::string, int> STRING_TO_UPLOAD_OPERATION_MAP {
    { "NONE", UploadOperation::NONE },
    { "TEST", UploadOperation::TEST },
    { "LIVE", UploadOperation::LIVE }
};
const std::map<int, std::string> UPLOAD_OPERATION_TO_STRING_MAP {
    { UploadOperation::NONE, "NONE" },
    { UploadOperation::TEST, "TEST" },
    { UploadOperation::LIVE, "LIVE" }
};


std::string GetHostTranslationServerUrl() {
    const IniFile ini(UBTools::GetTuelibPath() + "zotero.conf");
    return ini.getString("Server", "url");
}


const std::map<GlobalParams::IniKey, std::string> GlobalParams::KEY_TO_STRING_MAP {
    { ENHANCEMENT_MAPS_DIRECTORY,                 "enhancement_maps_directory" },
    { GROUP_NAMES,                                "groups" },
    { STRPTIME_FORMAT_STRING,                     "common_strptime_format" },
    { SKIP_ONLINE_FIRST_ARTICLES_UNCONDITIONALLY, "skip_online_first_articles_unconditionally" },
    { DOWNLOAD_DELAY_DEFAULT,                     "default_download_delay_time" },
    { DOWNLOAD_DELAY_MAX,                         "max_download_delay_time" },
    { REVIEW_REGEX,                               "zotero_review_regex" },
    { RSS_HARVEST_INTERVAL,                       "journal_rss_harvest_interval" },
    { RSS_FORCE_PROCESS_FEEDS_WITH_NO_PUB_DATES,  "force_process_feeds_with_no_pub_dates" },
    { TIMEOUT_CRAWL_OPERATION,                    "timeout_crawl_operation" },
    { TIMEOUT_DOWNLOAD_REQUEST,                   "timeout_download_request" },
};

static const auto PREFIX_DEFAULT_DOWNLOAD_DELAY_TIME("default_download_delay_time_");
static const auto PREFIX_MAX_DOWNLOAD_DELAY_TIME("max_download_delay_time_");
static const auto PREFIX_OVERRIDE_JSON_FIELD("override_json_field_");
static const auto PREFIX_SUPPRESS_JSON_FIELD("suppress_json_field_");
static const auto PREFIX_EXCLUDE_JSON_FIELD("exclude_if_json_field_");
static const auto PREFIX_ADD_MARC_FIELD("add_marc_field_");
static const auto PREFIX_REMOVE_MARC_FIELD("remove_marc_field_");
static const auto PREFIX_EXCLUDE_MARC_FIELD("exclude_if_marc_field_");


bool DownloadDelayParams::IsValidIniEntry(const IniFile::Entry &entry) {
    return (StringUtil::StartsWith(entry.name_, PREFIX_DEFAULT_DOWNLOAD_DELAY_TIME)
            or StringUtil::StartsWith(entry.name_, PREFIX_MAX_DOWNLOAD_DELAY_TIME));
}


DownloadDelayParams::DownloadDelayParams(const IniFile::Section &config_section) {
    default_delay_in_ms_ = 0;
    max_delay_in_ms_ = 0;
    for (const auto &entry : config_section) {
        if (entry.name_ == GlobalParams::GetIniKeyString(GlobalParams::DOWNLOAD_DELAY_DEFAULT))
            default_delay_in_ms_ = StringUtil::ToUnsigned(entry.value_);
        else if (entry.name_ == GlobalParams::GetIniKeyString(GlobalParams::DOWNLOAD_DELAY_MAX))
            max_delay_in_ms_ = StringUtil::ToUnsigned(entry.value_);
        else if (StringUtil::StartsWith(entry.name_, PREFIX_DEFAULT_DOWNLOAD_DELAY_TIME)) {
            const auto domain_name(entry.name_.substr(__builtin_strlen(PREFIX_DEFAULT_DOWNLOAD_DELAY_TIME)));
            domain_to_default_delay_map_[domain_name] = StringUtil::ToUnsigned(entry.value_);
        } else if (StringUtil::StartsWith(entry.name_, PREFIX_MAX_DOWNLOAD_DELAY_TIME)) {
            const auto domain_name(entry.name_.substr(__builtin_strlen(PREFIX_MAX_DOWNLOAD_DELAY_TIME)));
            domain_to_default_delay_map_[domain_name] = StringUtil::ToUnsigned(entry.value_);
        }
    }
}


bool ZoteroMetadataParams::IsValidIniEntry(const IniFile::Entry &entry) {
    return (StringUtil::StartsWith(entry.name_, PREFIX_OVERRIDE_JSON_FIELD)
            or StringUtil::StartsWith(entry.name_, PREFIX_SUPPRESS_JSON_FIELD)
            or StringUtil::StartsWith(entry.name_, PREFIX_EXCLUDE_JSON_FIELD));
}


ZoteroMetadataParams::ZoteroMetadataParams(const IniFile::Section &config_section) {
    for (const auto &entry : config_section) {
        if (StringUtil::StartsWith(entry.name_, PREFIX_OVERRIDE_JSON_FIELD)) {
            const auto field_name(entry.name_.substr(__builtin_strlen(PREFIX_OVERRIDE_JSON_FIELD)));
            fields_to_override_.insert(std::make_pair(field_name, entry.value_));
        } else if (StringUtil::StartsWith(entry.name_, PREFIX_SUPPRESS_JSON_FIELD)) {
            const auto field_name(entry.name_.substr(__builtin_strlen(PREFIX_SUPPRESS_JSON_FIELD)));
            fields_to_suppress_.insert(std::make_pair(field_name,
                                       std::unique_ptr<ThreadSafeRegexMatcher>(new ThreadSafeRegexMatcher(entry.value_))));
        } else if (StringUtil::StartsWith(entry.name_, PREFIX_EXCLUDE_JSON_FIELD)) {
            const auto metadata_name(entry.name_.substr(__builtin_strlen(PREFIX_EXCLUDE_JSON_FIELD)));
            exclusion_filters_.insert(std::make_pair(metadata_name,
                                      std::unique_ptr<ThreadSafeRegexMatcher>(new ThreadSafeRegexMatcher(entry.value_))));
        }
    }
}


bool MarcMetadataParams::IsValidIniEntry(const IniFile::Entry &entry) {
    return (StringUtil::StartsWith(entry.name_, PREFIX_ADD_MARC_FIELD)
            or StringUtil::StartsWith(entry.name_, PREFIX_REMOVE_MARC_FIELD)
            or StringUtil::StartsWith(entry.name_, PREFIX_EXCLUDE_MARC_FIELD));
}


MarcMetadataParams::MarcMetadataParams(const IniFile::Section &config_section) {
    for (const auto &entry : config_section) {
        if (StringUtil::StartsWith(entry.name_, PREFIX_ADD_MARC_FIELD))
            fields_to_add_.emplace_back(entry.value_);
        else if (StringUtil::StartsWith(entry.name_, PREFIX_EXCLUDE_MARC_FIELD)) {
            const auto field_name(entry.name_.substr(__builtin_strlen(PREFIX_EXCLUDE_MARC_FIELD)));
            if (field_name.length() != MARC::Record::TAG_LENGTH and field_name.length() != MARC::Record::TAG_LENGTH + 1)
                LOG_ERROR("invalid exclusion field name '" + field_name + "'! expected format: <tag> or <tag><subfield_code>");

            exclusion_filters_.insert(std::make_pair(field_name,
                                      std::unique_ptr<ThreadSafeRegexMatcher>(new ThreadSafeRegexMatcher(entry.value_))));
        } else if (StringUtil::StartsWith(entry.name_, PREFIX_REMOVE_MARC_FIELD)) {
            const auto field_name(entry.name_.substr(__builtin_strlen(PREFIX_REMOVE_MARC_FIELD)));
            if (field_name.length() != MARC::Record::TAG_LENGTH + 1)
                LOG_ERROR("invalid removal filter name '" + field_name + "'! expected format: <tag><subfield_code>");

            fields_to_remove_.insert(std::make_pair(field_name,
                                     std::unique_ptr<ThreadSafeRegexMatcher>(new ThreadSafeRegexMatcher(entry.value_))));
        }
    }
}


std::string GlobalParams::GetIniKeyString(const IniKey ini_key) {
    const auto key_and_string(KEY_TO_STRING_MAP.find(ini_key));
    if (key_and_string == KEY_TO_STRING_MAP.end())
        LOG_ERROR("invalid GlobalParams INI key '" + std::to_string(ini_key) + "'");
    return key_and_string->second;
}


GlobalParams::GlobalParams(const IniFile::Section &config_section) {
    skip_online_first_articles_unconditonally_ = false;
    rss_harvester_operation_params_.harvest_interval_ = 0;
    rss_harvester_operation_params_.force_process_feeds_with_no_pub_dates_ = false;

    // Translation server URL is special-cased
    translation_server_url_ = GetHostTranslationServerUrl();

    enhancement_maps_directory_ = config_section.getString(GetIniKeyString(ENHANCEMENT_MAPS_DIRECTORY));
    group_names_ = config_section.getString(GetIniKeyString(GROUP_NAMES));
    strptime_format_string_ = config_section.getString(GetIniKeyString(STRPTIME_FORMAT_STRING));
    skip_online_first_articles_unconditonally_ = config_section.getBool(GetIniKeyString(SKIP_ONLINE_FIRST_ARTICLES_UNCONDITIONALLY));
    timeout_crawl_operation_ = config_section.getUnsigned(GetIniKeyString(TIMEOUT_CRAWL_OPERATION)) * 1000;
    timeout_download_request_ = config_section.getUnsigned(GetIniKeyString(TIMEOUT_DOWNLOAD_REQUEST)) * 1000;
    rss_harvester_operation_params_.harvest_interval_ = config_section.getUnsigned(GetIniKeyString(RSS_HARVEST_INTERVAL));
    rss_harvester_operation_params_.force_process_feeds_with_no_pub_dates_ = config_section.getBool(GetIniKeyString(RSS_FORCE_PROCESS_FEEDS_WITH_NO_PUB_DATES));

    const auto review_regex(config_section.getString(GetIniKeyString(REVIEW_REGEX), ""));
    if (not review_regex.empty())
        review_regex_.reset(new ThreadSafeRegexMatcher(review_regex));

    zotero_metadata_params_ = ZoteroMetadataParams(config_section);
    marc_metadata_params_ = MarcMetadataParams(config_section);

    if (not strptime_format_string_.empty()) {
        if (strptime_format_string_[0] == '(')
            LOG_ERROR("Cannot specify locale in global strptime_format");
    }

    download_delay_params_ = DownloadDelayParams(config_section);

    CheckIniSection(config_section, GlobalParams::KEY_TO_STRING_MAP,
                    { DownloadDelayParams::IsValidIniEntry,
                      ZoteroMetadataParams::IsValidIniEntry,
                      MarcMetadataParams::IsValidIniEntry });
}


const std::map<GroupParams::IniKey, std::string> GroupParams::KEY_TO_STRING_MAP {
    { USER_AGENT,                       "user_agent" },
    { ISIL,                             "isil" },
    { OUTPUT_FOLDER,                    "output_folder" },
    { AUTHOR_SWB_LOOKUP_URL,            "author_swb_lookup_url" },
    { AUTHOR_LOBID_LOOKUP_QUERY_PARAMS, "author_lobid_lookup_query_params" },
};


GroupParams::GroupParams(const IniFile::Section &group_section) {
    name_ = group_section.getSectionName();
    user_agent_ = group_section.getString(GetIniKeyString(USER_AGENT));
    isil_ = group_section.getString(GetIniKeyString(ISIL));
    output_folder_ = group_section.getString(GetIniKeyString(OUTPUT_FOLDER));
    author_swb_lookup_url_ = group_section.getString(GetIniKeyString(AUTHOR_SWB_LOOKUP_URL));
    author_lobid_lookup_query_params_ = group_section.getString(GetIniKeyString(AUTHOR_LOBID_LOOKUP_QUERY_PARAMS), "");

    CheckIniSection(group_section, GroupParams::KEY_TO_STRING_MAP);
}


std::string GroupParams::GetIniKeyString(const IniKey ini_key) {
    const auto key_and_string(KEY_TO_STRING_MAP.find(ini_key));
    if (key_and_string == KEY_TO_STRING_MAP.end())
        LOG_ERROR("invalid GroupParams INI key '" + std::to_string(ini_key) + "'");
    return key_and_string->second;
}


JournalParams::JournalParams(const GlobalParams &global_params) {
    zeder_id_ = DEFAULT_ZEDER_ID;
    zeder_newly_synced_entry_ = false;
    name_ = "Default Journal";
    group_ = "Default Group";
    entry_point_url_ = "Default URL";
    harvester_operation_ = HarvesterOperation::DIRECT;
    upload_operation_ = UploadOperation::NONE;
    ppn_.online_ = "Default PPN";
    issn_.online_ = "Default ISSN";
    strptime_format_string_ = global_params.strptime_format_string_;
    update_window_ = 0;
    crawl_params_.max_crawl_depth_ = 1;
}


const std::map<JournalParams::IniKey, std::string> JournalParams::KEY_TO_STRING_MAP {
    { ZEDER_ID,                 "zeder_id"                  },
    { ZEDER_MODIFIED_TIME,      "zeder_modified_time"       },
    { ZEDER_NEWLY_SYNCED_ENTRY, "zeder_newly_synced_entry"  },
    { GROUP,                    "zotero_group"              },
    { ENTRY_POINT_URL,          "zotero_url"                },
    { HARVESTER_OPERATION,      "zotero_type"               },
    { UPLOAD_OPERATION,         "zotero_delivery_mode"      },
    { ONLINE_PPN,               "online_ppn"                },
    { PRINT_PPN,                "print_ppn"                 },
    { ONLINE_ISSN,              "online_issn"               },
    { PRINT_ISSN,               "print_issn"                },
    { SSGN,                     "ssgn"                      },
    { LICENSE,                  "license"                   },
    { STRPTIME_FORMAT_STRING,   "zotero_strptime_format"    },
    { UPDATE_WINDOW,            "zotero_update_window"      },
    { REVIEW_REGEX,             "zotero_review_regex"       },
    { EXPECTED_LANGUAGES,       "zotero_expected_languages" },
    { CRAWL_MAX_DEPTH,          "zotero_max_crawl_depth"    },
    { CRAWL_EXTRACTION_REGEX,   "zotero_extraction_regex"   },
    { CRAWL_URL_REGEX,          "zotero_crawl_url_regex"    },
};

const std::map<std::string, JournalParams::IniKey> JournalParams::STRING_TO_KEY_MAP {
    { "zeder_id",                  ZEDER_ID                 },
    { "zeder_modified_time",       ZEDER_MODIFIED_TIME      },
    { "zeder_newly_synced_entry",  ZEDER_NEWLY_SYNCED_ENTRY },
    { "zotero_group",              GROUP                    },
    { "zotero_url",                ENTRY_POINT_URL          },
    { "zotero_type",               HARVESTER_OPERATION      },
    { "zotero_delivery_mode",      UPLOAD_OPERATION         },
    { "online_ppn",                ONLINE_PPN               },
    { "print_ppn",                 PRINT_PPN                },
    { "online_issn",               ONLINE_ISSN              },
    { "print_issn",                PRINT_ISSN               },
    { "ssgn",                      SSGN                     },
    { "license",                   LICENSE                  },
    { "zotero_strptime_format",    STRPTIME_FORMAT_STRING   },
    { "zotero_update_window",      UPDATE_WINDOW            },
    { "zotero_review_regex",       REVIEW_REGEX             },
    { "zotero_expected_languages", EXPECTED_LANGUAGES       },
    { "zotero_max_crawl_depth",    CRAWL_MAX_DEPTH          },
    { "zotero_extraction_regex",   CRAWL_EXTRACTION_REGEX   },
    { "zotero_crawl_url_regex",    CRAWL_URL_REGEX          },
};


JournalParams::JournalParams(const IniFile::Section &journal_section, const GlobalParams &global_params) {
    zeder_id_ = journal_section.getUnsigned(GetIniKeyString(ZEDER_ID));
    zeder_newly_synced_entry_ = journal_section.getBool(GetIniKeyString(ZEDER_NEWLY_SYNCED_ENTRY), false);
    name_ = journal_section.getSectionName();
    group_ = journal_section.getString(GetIniKeyString(GROUP));
    entry_point_url_ = journal_section.getString(GetIniKeyString(ENTRY_POINT_URL));
    harvester_operation_ = static_cast<HarvesterOperation>(journal_section.getEnum(GetIniKeyString(HARVESTER_OPERATION),
                                                           STRING_TO_HARVEST_OPERATION_MAP));
    upload_operation_ = static_cast<UploadOperation>(journal_section.getEnum(GetIniKeyString(UPLOAD_OPERATION),
                                                     STRING_TO_UPLOAD_OPERATION_MAP, UploadOperation::NONE));
    ppn_.online_ = journal_section.getString(GetIniKeyString(ONLINE_PPN), "");
    ppn_.print_ = journal_section.getString(GetIniKeyString(PRINT_PPN), "");
    issn_.online_ = journal_section.getString(GetIniKeyString(ONLINE_ISSN), "");
    issn_.print_ = journal_section.getString(GetIniKeyString(PRINT_ISSN), "");
    strptime_format_string_ = journal_section.getString(GetIniKeyString(STRPTIME_FORMAT_STRING), "");
    if (not global_params.strptime_format_string_.empty()) {
        if (not strptime_format_string_.empty())
            strptime_format_string_ += '|';

        strptime_format_string_ += global_params.strptime_format_string_;
    }
    update_window_ = journal_section.getUnsigned(GetIniKeyString(UPDATE_WINDOW), 0);
    ssgn_ = journal_section.getString(GetIniKeyString(SSGN), "");
    license_ = journal_section.getString(GetIniKeyString(LICENSE), "");

    const auto review_regex(journal_section.getString(GetIniKeyString(REVIEW_REGEX), ""));
    if (not review_regex.empty())
        review_regex_.reset(new ThreadSafeRegexMatcher(review_regex));

    const std::string expected_languages(journal_section.getString(GetIniKeyString(EXPECTED_LANGUAGES), ""));
    if (not ParseExpectedLanguages(expected_languages, &language_params_))
        LOG_ERROR("invalid setting for expected languages: \"" + expected_languages + "\"");

    crawl_params_.max_crawl_depth_ = journal_section.getUnsigned(GetIniKeyString(CRAWL_MAX_DEPTH), 0);
    const auto extraction_regex(journal_section.getString(GetIniKeyString(CRAWL_EXTRACTION_REGEX), ""));
    if (not extraction_regex.empty())
        crawl_params_.extraction_regex_.reset(new ThreadSafeRegexMatcher(extraction_regex));

    const auto crawl_regex(journal_section.getString(GetIniKeyString(CRAWL_URL_REGEX), ""));
    if (not crawl_regex.empty())
        crawl_params_.crawl_url_regex_.reset(new ThreadSafeRegexMatcher(crawl_regex));

    // repeatable fields
    zotero_metadata_params_ = ZoteroMetadataParams(journal_section);
    marc_metadata_params_ = MarcMetadataParams(journal_section);

    CheckIniSection(journal_section, JournalParams::KEY_TO_STRING_MAP,
                    { ZoteroMetadataParams::IsValidIniEntry, MarcMetadataParams::IsValidIniEntry });
}


std::string JournalParams::GetIniKeyString(const IniKey ini_key) {
    const auto key_and_string(KEY_TO_STRING_MAP.find(ini_key));
    if (key_and_string == KEY_TO_STRING_MAP.end())
        LOG_ERROR("invalid JournalParams INI key '" + std::to_string(ini_key) + "'");
    return key_and_string->second;
}


JournalParams::IniKey JournalParams::GetIniKey(const std::string &ini_key_string) {
    const auto string_and_key(STRING_TO_KEY_MAP.find(ini_key_string));
    if (string_and_key == STRING_TO_KEY_MAP.end())
        LOG_ERROR("invalid JournalParams INI key string '" + ini_key_string + "'");
    return string_and_key->second;
}


void LoadHarvesterConfigFile(const std::string &config_filepath, std::unique_ptr<GlobalParams> * const global_params,
                             std::vector<std::unique_ptr<GroupParams>> * const group_params,
                             std::vector<std::unique_ptr<JournalParams>> * const journal_params,
                             std::unique_ptr<IniFile> * const config_file,
                             const IniFile::Section config_overrides)
{
    std::unique_ptr<IniFile> ini(new IniFile(config_filepath));

    global_params->reset(new Config::GlobalParams(*ini->getSection("")));

    std::set<std::string> group_names;
    StringUtil::Split((*global_params)->group_names_, ',', &group_names, /* suppress_empty_components = */ true);

    for (const auto &group_name : group_names)
        group_params->emplace_back(new Config::GroupParams(*ini->getSection(group_name)));

    for (const auto &section : *ini) {
        if (section.getSectionName().empty())
            continue;
        else if (group_names.find(section.getSectionName()) != group_names.end())
            continue;

        if (config_overrides.size() > 0) {
            IniFile::Section section2(section);
            for (const auto &override_entry : config_overrides) {
                section2.insert(override_entry.name_, override_entry.value_, override_entry.comment_,
                               IniFile::Section::DupeInsertionBehaviour::OVERWRITE_EXISTING_VALUE);
            }
            journal_params->emplace_back(new Config::JournalParams(section2, **global_params));
        } else
            journal_params->emplace_back(new Config::JournalParams(section, **global_params));
    }

    if (config_file != nullptr)
        config_file->reset(ini.release());
}


bool IsAllowedLanguage(const std::string &language) {
    return IsNormalizedLanguage(language) or
           TranslationUtil::IsValidInternational2LetterCode(language) or
           TranslationUtil::IsValidGerman3Or4LetterCode(language);
}


bool IsNormalizedLanguage(const std::string &language) {
    return TranslationUtil::IsValidFake3Or4LetterEnglishLanguagesCode(language);
}


std::string GetNormalizedLanguage(const std::string &language) {
    std::string normalized_language(language);
    if (TranslationUtil::IsValidInternational2LetterCode(normalized_language))
        normalized_language = TranslationUtil::MapInternational2LetterCodeToGerman3Or4LetterCode(normalized_language);
    // Here we do NOT use elseif, since we want to continue the conversion if the first mapping was successful
    if (TranslationUtil::IsValidGerman3Or4LetterCode(normalized_language))
        normalized_language = TranslationUtil::MapGermanLanguageCodesToFake3LetterEnglishLanguagesCodes(normalized_language);
    if (not IsNormalizedLanguage(normalized_language))
        throw std::runtime_error("unable to normalize language: \"" + language + "\"");
    return normalized_language;
}


bool ParseExpectedLanguages(const std::string &expected_languages_string, LanguageParams * const language_params) {
    // Setting is optional, so empty value is allowed (use defaults)
    language_params->reset();
    if (expected_languages_string.empty())
        return true;

    // force? (deprecated, treat as invalid)
    std::string expected_languages(expected_languages_string);
    if (expected_languages[0] == '*')
        return false;

    // source text fields
    const auto field_separator_pos(expected_languages.find(':'));
    if (field_separator_pos != std::string::npos) {
        const std::string source_text_fields = expected_languages.substr(0, field_separator_pos);
        if (source_text_fields != "title" and source_text_fields != "abstract" and source_text_fields != "title+abstract") {
            LOG_WARNING("invalid value for source text fields: '" + source_text_fields + "'");
            return false;
        }

        language_params->source_text_fields_ = source_text_fields;
        expected_languages = expected_languages.substr(field_separator_pos + 1);
    }

    // language candidates
    std::set<std::string> expected_languages_candidates;
    StringUtil::Split(expected_languages, ',', &expected_languages_candidates, /* suppress_empty_components = */true);
    if (expected_languages_candidates.size() == 0)
        return false;
    for (const auto &expected_language : expected_languages_candidates) {
        if (not IsAllowedLanguage(expected_language)) {
            LOG_WARNING("invalid language '" + expected_language + "'!");
            return false;
        }

        expected_languages_candidates.emplace(GetNormalizedLanguage(expected_language));
    }

    language_params->expected_languages_ = expected_languages_candidates;
    return true;
}


} // end namespace Config


} // end namespace ZoteroHarvester
