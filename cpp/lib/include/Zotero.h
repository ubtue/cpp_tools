/** \brief Interaction with Zotero Translation Server
 *         - For a list of Zotero field types ("itemFields") in JSON, see
 *           https://github.com/zotero/zotero/blob/master/chrome/locale/de/zotero/zotero.properties#L409
 *  \author Mario Trojan
 *
 *  \copyright 2018 Universitätsbibliothek Tübingen.  All rights reserved.
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


#include <memory>
#include <ctime>
#include <kchashdb.h>
#include <unordered_map>
#include "BSZTransform.h"
#include "DbConnection.h"
#include "Downloader.h"
#include "DownloadTracker.h"
#include "IniFile.h"
#include "JSON.h"
#include "MARC.h"
#include "RegexMatcher.h"
#include "SimpleCrawler.h"
#include "TimeLimit.h"
#include "UnsignedPair.h"
#include "Url.h"


namespace BSZTransform { struct AugmentMaps; } // forward declaration


namespace Zotero {


enum HarvesterType { RSS, CRAWL, DIRECT };


extern const std::map<HarvesterType, std::string> HARVESTER_TYPE_TO_STRING_MAP;


const std::map<std::string, int> STRING_TO_HARVEST_TYPE_MAP { { "RSS", static_cast<int>(Zotero::HarvesterType::RSS) },
                                                              { "DIRECT", static_cast<int>(Zotero::HarvesterType::DIRECT) },
                                                              { "CRAWL", static_cast<int>(Zotero::HarvesterType::CRAWL) } };


struct Creator {
    std::string first_name;
    std::string last_name;
    std::string type;
    std::string ppn;
    std::string gnd_number;
};


struct CustomNodeParameters {
    std::string issn_normalized;
    std::string parent_journal_name;
    std::string harvest_url;
    std::string physical_form;
    std::string year;
    std::string pages;
    std::string volume;
    std::string license;
    std::string ssg_numbers;
    std::string journal_ppn;
    std::vector<Creator> creators;
    std::string comment;
    std::string date_normalized;
    std::string isil;
};


struct ItemParameters {
    std::string item_type;
    std::string publication_title;
    std::string abbreviated_publication_title;
    std::string language;
    std::string abstract_note;
    std::string website_title;
    std::string doi;
    std::string copyright;
    std::vector<Creator> creators;
    std::string url;
    std::string year;
    std::string pages;
    std::string volume;
    std::string date;
    std::string title;
    std::string short_title;
    std::string issue;
    std::string isil;
    // Additional item parameters
    std::string superior_ppn; // Generated on our side
    std::string issn;
    std::string license;
    std::vector<std::string> keywords;
    std::vector<std::string> ssg_numbers;
    std::string physical_form;
    std::string parent_journal_name;
    std::string harvest_url;
    std::map<std::string, std::string> notes_key_value_pairs_; // Abuse of the "notes" field to pass thru non-standard values
};


// native supported formats, see https://github.com/zotero/translation-server/blob/master/src/server_translation.js#L31-43
// also allowed: json, marc21 and marcxml
extern const std::vector<std::string> EXPORT_FORMATS;


const std::string GetCreatorTypeForMarc21(const std::string &zotero_creator_type);


/**
 * Functions are named like endpoints, see
 * https://github.com/zotero/translation-server
 */
namespace TranslationServer {


/** \brief get url for zotero translation server based on local machine configuration */
const Url GetUrl();


/** \brief Use builtin translator to convert JSON to output format. */
bool Export(const Url &zts_server_url, const TimeLimit &time_limit, Downloader::Params downloader_params,
            const std::string &format, const std::string &json, std::string * const response_body,
            std::string * const error_message);

/** \brief Use builtin translator to convert input format to JSON. */
bool Import(const Url &zts_server_url, const TimeLimit &time_limit, Downloader::Params downloader_params,
            const std::string &input_content, std::string * const output_json, std::string * const error_message);

/** \brief Download single URL and return as JSON. (If harvested_html is not empty, URL is not downloaded again.) */
bool Web(const Url &zts_server_url, const TimeLimit &time_limit, Downloader::Params downloader_params,
         const Url &harvest_url, std::string * const response_body, unsigned * response_code,
         std::string * const error_message);

/** \brief This function is used if we get a "300 - multiple" response, to paste the response body back to the server.
 *         This way we get a JSON array with all downloaded results.
 */
bool Web(const Url &zts_server_url, const TimeLimit &time_limit, Downloader::Params downloader_params,
         const std::string &request_body, std::string * const response_body, unsigned * response_code,
         std::string * const error_message);


} // namespace TranslationServer


extern const std::string DEFAULT_SUBFIELD_CODE;


// Default timeout values in milliseconds
constexpr unsigned DEFAULT_CONVERSION_TIMEOUT = 60000;
constexpr unsigned DEFAULT_TIMEOUT = 10000;
constexpr unsigned DEFAULT_MIN_URL_PROCESSING_TIME = 200;


struct GroupParams {
    std::string name_;
    std::string user_agent_;
    std::string isil_;
    std::string bsz_upload_group_;
    std::string author_ppn_lookup_url_;
    std::string author_gnd_lookup_query_params_;
    std::vector<std::string> additional_fields_;
};


void LoadGroup(const IniFile::Section &section, std::unordered_map<std::string, GroupParams> * const group_name_to_params_map);


/** \brief Parameters that apply to all sites equally. */
struct GobalAugmentParams {
    BSZTransform::AugmentMaps * const maps_;
public:
    explicit GobalAugmentParams(BSZTransform::AugmentMaps * const maps): maps_(maps) { }
};


/** \brief Parameters that apply to single sites only. */
struct SiteParams {
    // So that we don't have to pass through two arguments everywhere.
    GobalAugmentParams *global_params_;
    GroupParams *group_params_;

    std::string parent_journal_name_;
    std::string parent_ISSN_print_;
    std::string parent_ISSN_online_;
    std::string parent_PPN_;
    std::string strptime_format_;
    std::vector<MARC::EditInstruction> marc_edit_instructions_;
    std::unique_ptr<RegexMatcher> extraction_regex_;
    BSZUpload::DeliveryMode delivery_mode_;
    std::vector<std::string> additional_fields_;
    std::vector<std::string> non_standard_metadata_fields_;
public:
};


/** \brief  This function can be used to augment  Zotero JSON structure with information from AugmentParams.
 *  \param  object_node     The JSON ObjectNode with Zotero JSON structure of a single dataset
 *  \param  harvest_maps    The map files to apply.
 */
void AugmentJson(const std::shared_ptr<JSON::ObjectNode> &object_node, const SiteParams &site_params);


// forward declaration
class FormatHandler;
class HarvesterErrorLogger;


struct HarvestParams {
    Url zts_server_url_;
    TimeLimit min_url_processing_time_ = DEFAULT_MIN_URL_PROCESSING_TIME;
    unsigned harvested_url_count_ = 0;
    std::string user_agent_;
    FormatHandler *format_handler_;
};


class FormatHandler {
protected:
    DownloadTracker download_tracker_;
    std::string output_format_;
    std::string output_file_;
    SiteParams *site_params_;
    const std::shared_ptr<const HarvestParams> &harvest_params_;
protected:
    FormatHandler(DbConnection * const db_connection, const std::string &output_format, const std::string &output_file,
                  const std::shared_ptr<const HarvestParams> &harvest_params)
        : download_tracker_(db_connection), output_format_(output_format), output_file_(output_file),
          site_params_(nullptr), harvest_params_(harvest_params)
        { }
public:
    virtual ~FormatHandler() = default;

    inline void setAugmentParams(SiteParams * const new_site_params) { site_params_ = new_site_params; }
    inline DownloadTracker &getDownloadTracker() { return download_tracker_; }

    /** \brief Convert & write single record to output file */
    virtual std::pair<unsigned, unsigned> processRecord(const std::shared_ptr<const JSON::ObjectNode> &object_node) = 0;

    // The output format must be one of "bibtex", "biblatex", "bookmarks", "coins", "csljson", "mods", "refer",
    // "rdf_bibliontology", "rdf_dc", "rdf_zotero", "ris", "wikipedia", "tei", "json", "marc-21", or "marc-xml".
    static std::unique_ptr<FormatHandler> Factory(DbConnection * const db_connection, const std::string &output_format,
                                                  const std::string &output_file,
                                                  const std::shared_ptr<const HarvestParams> &harvest_params);
     inline BSZUpload::DeliveryMode getDeliveryMode() { return site_params_ == nullptr ? BSZUpload::NONE : site_params_->delivery_mode_; }
};


class JsonFormatHandler final : public FormatHandler {
    unsigned record_count_;
    File *output_file_object_;
public:
    JsonFormatHandler(DbConnection * const db_connection, const std::string &output_format, const std::string &output_file,
                      const std::shared_ptr<const HarvestParams> &harvest_params);
    virtual ~JsonFormatHandler();
    virtual std::pair<unsigned, unsigned> processRecord(const std::shared_ptr<const JSON::ObjectNode> &object_node) override;
};


class ZoteroFormatHandler final : public FormatHandler {
    unsigned record_count_;
    std::string json_buffer_;
public:
    ZoteroFormatHandler(DbConnection * const db_connection, const std::string &output_format, const std::string &output_file,
                        const std::shared_ptr<const HarvestParams> &harvest_params);
    virtual ~ZoteroFormatHandler();
    virtual std::pair<unsigned, unsigned> processRecord(const std::shared_ptr<const JSON::ObjectNode> &object_node) override;
};


class MarcFormatHandler final : public FormatHandler {
    std::unique_ptr<MARC::Writer> marc_writer_;
public:
    MarcFormatHandler(DbConnection * const db_connection, const std::string &output_file,
                      const std::shared_ptr<const HarvestParams> &harvest_params, const std::string &output_format = "");
    virtual ~MarcFormatHandler() = default;
    virtual std::pair<unsigned, unsigned> processRecord(const std::shared_ptr<const JSON::ObjectNode> &object_node) override;
    MARC::Writer *getWriter() { return marc_writer_.get(); }
private:
    inline std::string CreateSubfieldFromStringNode(const std::string &key, const std::shared_ptr<const JSON::JSONNode> node,
                                                    const std::string &tag, const char subfield_code,
                                                    MARC::Record * const marc_record, const char indicator1 = ' ',
                                                    const char indicator2 = ' ')
    {
        const std::shared_ptr<const JSON::StringNode> string_node(JSON::JSONNode::CastToStringNodeOrDie(key, node));
        const std::string value(string_node->getValue());
        marc_record->insertField(tag, { { subfield_code, value } }, indicator1, indicator2);
        return value;
    }

    inline std::string CreateSubfieldFromStringNode(const std::pair<std::string, std::shared_ptr<JSON::JSONNode>> &key_and_node,
                                                    const std::string &tag, const char subfield_code,
                                                    MARC::Record * const marc_record, const char indicator1 = ' ',
                                                    const char indicator2 = ' ')
    {
        return CreateSubfieldFromStringNode(key_and_node.first, key_and_node.second, tag, subfield_code, marc_record,
                                            indicator1, indicator2);
    }

    void ExtractKeywords(std::shared_ptr<const JSON::JSONNode> tags_node, const std::string &issn,
                         const std::unordered_map<std::string, std::string> &ISSN_to_keyword_field_map,
                         MARC::Record * const new_record);

    void ExtractVolumeYearIssueAndPages(const JSON::ObjectNode &object_node,
                                        MARC::Record * const new_record);

    MARC::Record processJSON(const std::shared_ptr<const JSON::ObjectNode> &object_node, std::string * const url,
                             std::string * const publication_title, std::string * const abbreviated_publication_title,
                             std::string * const website_title);

    // Extracts information from the ubtue node
    void ExtractCustomNodeParameters(std::shared_ptr<const JSON::JSONNode> custom_node,
                                     struct CustomNodeParameters * const custom_node_parameters);

    void ExtractItemParameters(std::shared_ptr<const JSON::ObjectNode> object_node,
                               struct ItemParameters * const item_parameters);

    void GenerateMarcRecord(MARC::Record * const record, const struct ItemParameters &item_parameters);

    void MergeCustomParametersToItemParameters(struct ItemParameters * const item_parameters,
                                               struct CustomNodeParameters &custom_node_params);

    void HandleTrackingAndWriteRecord(const MARC::Record &new_record, BSZUpload::DeliveryMode delivery_mode,
                                  struct ItemParameters &item_params, unsigned * const previously_downloaded_count);
};


const std::shared_ptr<RegexMatcher> LoadSupportedURLsRegex(const std::string &map_directory_path);


/** \brief  Harvest a single URL.
 *  \param  harvest_url         The URL to harvest.
 *  \param  extraction_regex    Regex matcher for URLs that can be harvested.
 *  \param  harvest_params      The parameters for downloading.
 *  \param  site_params      Parameter for augmenting the Zotero JSON result.
 *  \param  harvested_html      If not empty, the HTML will be used for harvesting
 *                              instead of downloading the URL again.
 *                              However, if the page contains a list of multiple
 *                              items (e.g. HTML page with a search result),
 *                              all results will be downloaded.
 *  \param  log                 If true, additional statistics will be logged.
 *  \return count of all records / previously downloaded records => The number of newly downloaded records is the
 *          difference (first - second).
 */
std::pair<unsigned, unsigned> Harvest(const std::string &harvest_url, const std::shared_ptr<HarvestParams> harvest_params,
                                      const SiteParams &site_params, HarvesterErrorLogger * const error_logger, const bool verbose = true);


/** \brief Harvest metadate from a single site.
 *  \return count of all records / previously downloaded records => The number of newly downloaded records is the
 *          difference (first - second).
 */
UnsignedPair HarvestSite(const SimpleCrawler::SiteDesc &site_desc, const SimpleCrawler::Params &crawler_params,
                         const std::shared_ptr<RegexMatcher> &supported_urls_regex, const std::shared_ptr<HarvestParams> &harvest_params,
                         const SiteParams &site_params, HarvesterErrorLogger * const error_logger, File * const progress_file = nullptr);


/** \brief Harvest metadate from a single Web page.
 *  \return count of all records / previously downloaded records => The number of newly downloaded records is the
 *          difference (first - second).
 */
UnsignedPair HarvestURL(const std::string &url, const std::shared_ptr<HarvestParams> &harvest_params,
                        const SiteParams &site_params, HarvesterErrorLogger * const error_logger);


enum class RSSHarvestMode { VERBOSE, TEST, NORMAL };


/** \brief Harvest metadata from URL's referenced in an RSS or Atom feed.
 *  \param feed_url       Where to download the RSS feed.
 *  \param db_connection  A connection to a database w/ the structure as specified by .../cpp/data/ub_tools.sql. Not used when "mode"
 *                        is set to TEST.
 *  \return count of all records / previously downloaded records => The number of newly downloaded records is the
 *          difference (first - second).
 */
UnsignedPair HarvestSyndicationURL(const RSSHarvestMode mode, const std::string &feed_url,
                                   const std::shared_ptr<Zotero::HarvestParams> &harvest_params,
                                   const SiteParams &site_params, HarvesterErrorLogger * const error_logger,
                                   DbConnection * const db_connection);


class HarvesterErrorLogger {
public:
    enum ErrorType {
        UNKNOWN,
        ZTS_CONVERSION_FAILED,
        DOWNLOAD_MULTIPLE_FAILED,
        FAILED_TO_PARSE_JSON,
        ZTS_EMPTY_RESPONSE,
        BAD_STRPTIME_FORMAT
    };

    friend class Context;

    class Context {
        friend class HarvesterErrorLogger;

        HarvesterErrorLogger &parent_;
        std::string journal_name_;
        std::string harvest_url_;
    private:
        Context(HarvesterErrorLogger * const parent, const std::string &journal_name, const std::string &harvest_url)
         : parent_(*parent), journal_name_(journal_name), harvest_url_(harvest_url) {}
    public:
        void log(HarvesterErrorLogger::ErrorType error, const std::string &message) {
            parent_.log(error, journal_name_, harvest_url_, message);
        }
        void autoLog(const std::string &message) {
            parent_.autoLog(journal_name_, harvest_url_, message);
        }
    };
private:
    static const std::unordered_map<ErrorType, std::string> ERROR_KIND_TO_STRING_MAP;

    struct HarvesterError {
        ErrorType type;
        std::string message;
    };

    struct JournalErrors {
        std::unordered_map<std::string, HarvesterError> url_errors_;
        std::vector<HarvesterError> non_url_errors_;
    };

    std::unordered_map<std::string, JournalErrors> journal_errors_;
public:
    HarvesterErrorLogger() = default;
public:
    Context newContext(const std::string &journal_name, const std::string &harvest_url) {
        return Context(this, journal_name, harvest_url);
    }
    void log(ErrorType error, const std::string &journal_name, const std::string &harvest_url, const std::string &message,
             const bool write_to_stderr = true);

    // Used when the error message crosses API boundaries and cannot be logged at the point of inception
    void autoLog(const std::string &journal_name, const std::string &harvest_url, const std::string &message,
                 const bool write_to_stderr = true);
    void writeReport(const std::string &report_file_path) const;
};


} // namespace Zotero


namespace std {
    template <>
    struct hash<Zotero::HarvesterErrorLogger::ErrorType> {
        size_t operator()(const Zotero::HarvesterErrorLogger::ErrorType &harvester_error_type) const {
            // hash method here.
            return hash<int>()(harvester_error_type);
        }
    };
} // namespace std
