/** \brief Interaction with Zotero Translation Server
 *         public functions are named like endpoints
 *         see https://github.com/zotero/translation-server
 *  \author Dr. Johannes Ruscheinski
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
#include "Zotero.h"
#include <ctime>
#include <kchashdb.h>
#include <uuid/uuid.h>
#include "DbConnection.h"
#include "MiscUtil.h"
#include "SqlUtil.h"
#include "StringUtil.h"
#include "SyndicationFormat.h"
#include "TimeUtil.h"
#include "UrlUtil.h"
#include "WebUtil.h"
#include "util.h"


// Forward declaration:
class File;


namespace Zotero {


const std::string DEFAULT_SIMPLE_CRAWLER_CONFIG_PATH("/usr/local/var/lib/tuelib/zotero_crawler.conf");
const std::string ISSN_TO_PPN_MAP_PATH("/usr/local/var/lib/tuelib/issn_to_ppn.map");


const std::vector<std::string> EXPORT_FORMATS{
    "bibtex", "biblatex", "bookmarks", "coins", "csljson", "mods", "refer",
    "rdf_bibliontology", "rdf_dc", "rdf_zotero", "ris", "wikipedia", "tei",
    "json", "marc21", "marcxml"
};


const std::string DEFAULT_SUBFIELD_CODE("eng");


namespace {


// We try to be unique for the machine we're on.  Beyond that we may have a problem.
std::string GetNextSessionId() {
    static unsigned counter;
    static uint32_t uuid[4];
    if (unlikely(counter == 0))
        ::uuid_generate(reinterpret_cast<unsigned char *>(uuid));
    ++counter;
    return "ub_tools_zts_client_" + StringUtil::ToString(uuid[0]) + StringUtil::ToString(uuid[1])
           + StringUtil::ToString(uuid[2]) + StringUtil::ToString(uuid[3]) + "_" + StringUtil::ToString(counter);
}


std::string GetNextControlNumber() {
    static unsigned last_control_number;
    ++last_control_number;
    static const std::string prefix("ZTS");
    return prefix + StringUtil::PadLeading(std::to_string(last_control_number), 7, '0');
}


} // unnamed namespace


namespace TranslationServer {


bool ResponseCodeIndicatesSuccess(unsigned response_code, const std::string &response_body, std::string * const error_message) {
    const std::string response_code_string(StringUtil::ToString(response_code));
    const char response_code_category(response_code_string[0]);
    if (response_code_category == '4' or response_code_category == '5' or response_code_category == '9') {
        *error_message = "HTTP response " + response_code_string;
        if (not response_body.empty())
            *error_message += " (" + response_body + ")";
        return false;
    }
    return true;
}


bool Export(const Url &zts_server_url, const TimeLimit &time_limit, Downloader::Params downloader_params,
            const std::string &format, const std::string &json,
            std::string * const response_body, std::string * const error_message)
{
    const std::string endpoint_url(Url(zts_server_url.toString() + "/export?format=" + format));
    downloader_params.additional_headers_ = { "Content-Type: application/json" };
    downloader_params.post_data_ = json;

    Downloader downloader(endpoint_url, downloader_params, time_limit);
    if (downloader.anErrorOccurred()) {
        *error_message = downloader.getLastErrorMessage();
        return false;
    } else {
        *response_body = downloader.getMessageBody();
        return ResponseCodeIndicatesSuccess(downloader.getResponseCode(), *response_body, error_message);
    }
}


bool Import(const Url &zts_server_url, const TimeLimit &time_limit, Downloader::Params downloader_params,
            const std::string &input_content, std::string * const output_json, std::string * const error_message)
{
    const std::string endpoint_url(Url(zts_server_url.toString() + "/import"));
    downloader_params.post_data_ = input_content;

    Downloader downloader(endpoint_url, downloader_params, time_limit);
    if (downloader.anErrorOccurred()) {
        *error_message = downloader.getLastErrorMessage();
        return false;
    } else {
        *output_json = downloader.getMessageBody();
        return ResponseCodeIndicatesSuccess(downloader.getResponseCode(), *output_json, error_message);
    }
}


bool Web(const Url &zts_server_url, const TimeLimit &time_limit, Downloader::Params downloader_params,
         const Url &harvest_url, std::string * const response_body, unsigned * response_code,
         std::string * const error_message, const std::string &harvested_html)
{
    const std::string endpoint_url(Url(zts_server_url.toString() + "/web"));
    downloader_params.additional_headers_ = { "Accept: application/json", "Content-Type: application/json" };
    downloader_params.post_data_ = "{\"url\":\"" + JSON::EscapeString(harvest_url) + "\","
                                   + "\"sessionid\":\"" + JSON::EscapeString(GetNextSessionId()) + "\"";
    if (not harvested_html.empty()) {
        //downloader_params.post_data_ += ",\"cachedHTML\":\"" + JSON::EscapeString(harvested_html) + "\"";
        LOG_INFO("TODO: implement using cached html");
    }
    downloader_params.post_data_ += "}";

    Downloader downloader(endpoint_url, downloader_params, time_limit);
    if (downloader.anErrorOccurred()) {
        *error_message = downloader.getLastErrorMessage();
        return false;
    } else {
        *response_code = downloader.getResponseCode();
        *response_body = downloader.getMessageBody();
        return ResponseCodeIndicatesSuccess(*response_code, *response_body, error_message);
    }
}


} // namespace TranslationServer


std::unique_ptr<FormatHandler> FormatHandler::Factory(const std::string &previous_downloads_db_path, const std::string &output_format,
                                                      const std::string &output_file,
                                                      const std::shared_ptr<const HarvestParams> &harvest_params)
{
    if (output_format == "marcxml" or output_format == "marc21")
        return std::unique_ptr<FormatHandler>(new MarcFormatHandler(previous_downloads_db_path, output_file, harvest_params));
    else if (output_format == "json")
        return std::unique_ptr<FormatHandler>(new JsonFormatHandler(previous_downloads_db_path, output_format, output_file, harvest_params));
    else if (std::find(EXPORT_FORMATS.begin(), EXPORT_FORMATS.end(), output_format) != EXPORT_FORMATS.end())
        return std::unique_ptr<FormatHandler>(new ZoteroFormatHandler(previous_downloads_db_path, output_format, output_file,
                                                                      harvest_params));
    else
        LOG_ERROR("invalid output-format: " + output_format);
}


JsonFormatHandler::JsonFormatHandler(const std::string &previous_downloads_db_path, const std::string &output_format,
                                     const std::string &output_file, const std::shared_ptr<const HarvestParams> &harvest_params)
    : FormatHandler(previous_downloads_db_path, output_format, output_file, harvest_params), record_count_(0),
      output_file_object_(new File(output_file_, "w"))
{
    output_file_object_->write("[");
}


JsonFormatHandler::~JsonFormatHandler() {
    output_file_object_->write("]");
    delete output_file_object_;
}


std::pair<unsigned, unsigned> JsonFormatHandler::processRecord(const std::shared_ptr<const JSON::ObjectNode> &object_node) {
    if (record_count_ > 0)
        output_file_object_->write(",");
    output_file_object_->write(object_node->toString());
    ++record_count_;
    return std::make_pair(1, 0);
}


ZoteroFormatHandler::ZoteroFormatHandler(const std::string &previous_downloads_db_path, const std::string &output_format,
                                         const std::string &output_file, const std::shared_ptr<const HarvestParams> &harvest_params)
    : FormatHandler(previous_downloads_db_path, output_format, output_file, harvest_params), record_count_(0),
      json_buffer_("[")
{
}


ZoteroFormatHandler::~ZoteroFormatHandler() {
    json_buffer_ += "]";

    Downloader::Params downloader_params;
    std::string response_body;
    std::string error_message;
    if (not TranslationServer::Export(harvest_params_->zts_server_url_, DEFAULT_CONVERSION_TIMEOUT, downloader_params,
                                      output_format_, json_buffer_, &response_body, &error_message))
        LOG_ERROR("converting to target format failed: " + error_message);
    else
        FileUtil::WriteString(output_file_, response_body);
}


std::pair<unsigned, unsigned> ZoteroFormatHandler::processRecord(const std::shared_ptr<const JSON::ObjectNode> &object_node) {
    if (record_count_ > 0)
        json_buffer_ += ",";
    json_buffer_ += object_node->toString();
    ++record_count_;
    return std::make_pair(1, 0);
}


std::string GuessOutputFormat(const std::string &output_file) {
    switch (MARC::GuessFileType(output_file, /* read_file = */ false)) {
    case MARC::FileType::BINARY:
        return "marc21";
    case MARC::FileType::XML:
        return "marcxml";
    default:
        LOG_ERROR("we should *never* get here!");
    }
}


MarcFormatHandler::MarcFormatHandler(const std::string &previous_downloads_db_path, const std::string &output_file,
                                     const std::shared_ptr<const HarvestParams> &harvest_params)
    : FormatHandler(previous_downloads_db_path, GuessOutputFormat(output_file), output_file, harvest_params),
      marc_writer_(MARC::Writer::Factory(output_file_))
{
}


void MarcFormatHandler::ExtractKeywords(std::shared_ptr<const JSON::JSONNode> tags_node, const std::string &issn,
                                        const std::unordered_map<std::string, std::string> &ISSN_to_keyword_field_map,
                                        MARC::Record * const new_record)
{
    const std::shared_ptr<const JSON::ArrayNode> tags(JSON::JSONNode::CastToArrayNodeOrDie("tags", tags_node));

    // Where to stuff the data:
    std::string marc_field("653");
    char marc_subfield('a');
    if (not issn.empty()) {
        const auto issn_and_field_tag_and_subfield_code(ISSN_to_keyword_field_map.find(issn));
        if (issn_and_field_tag_and_subfield_code != ISSN_to_keyword_field_map.end()) {
            if (unlikely(issn_and_field_tag_and_subfield_code->second.length() != 3 + 1))
                LOG_ERROR("\"" + issn_and_field_tag_and_subfield_code->second
                          + "\" is not a valid MARC tag + subfield code! (Error in \"ISSN_to_keyword_field.map\"!)");
            marc_field    = issn_and_field_tag_and_subfield_code->second.substr(0, 3);
            marc_subfield =  issn_and_field_tag_and_subfield_code->second[3];
        }
    }

    for (const auto &tag : *tags) {
        const std::shared_ptr<const JSON::ObjectNode> tag_object(JSON::JSONNode::CastToObjectNodeOrDie("tag", tag));
        const std::shared_ptr<const JSON::JSONNode> tag_node(tag_object->getNode("tag"));
        if (tag_node == nullptr)
            LOG_ERROR("unexpected: tag object does not contain a \"tag\" entry!");
        else if (tag_node->getType() != JSON::JSONNode::STRING_NODE)
            LOG_ERROR("unexpected: tag object's \"tag\" entry is not a string node!");
        else
            CreateSubfieldFromStringNode("tag", tag_node, marc_field, marc_subfield, new_record);
    }
}


void MarcFormatHandler::ExtractVolumeYearIssueAndPages(const JSON::ObjectNode &object_node, MARC::Record * const new_record) {
    std::vector<MARC::Subfield> subfields;

    std::shared_ptr<const JSON::JSONNode> custom_node(object_node.getNode("ubtue"));
    if (custom_node != nullptr) {
        const std::shared_ptr<const JSON::ObjectNode>custom_object(JSON::JSONNode::CastToObjectNodeOrDie("ubtue", custom_node));
        std::string date_str(custom_object->getOptionalStringValue("date_normalized"));
        if (date_str.empty())
            date_str = custom_object->getOptionalStringValue("date_raw");

        const std::string STRPTIME_FORMAT(augment_params_->strptime_format_.empty() ? "%Y-%m-%d" : augment_params_->strptime_format_);
        const struct tm tm(TimeUtil::StringToStructTm(date_str, STRPTIME_FORMAT));
        subfields.emplace_back('j', std::to_string(tm.tm_year + 1900));
    }

    const std::string issue(object_node.getOptionalStringValue("issue"));
    if (not issue.empty())
        subfields.emplace_back('e', issue);

    const std::string pages(object_node.getOptionalStringValue("pages"));
    if (not pages.empty())
        subfields.emplace_back('h', pages);

    const std::string volume(object_node.getOptionalStringValue("volume"));
    if (not volume.empty())
        subfields.emplace_back('d', volume);

    if (not subfields.empty())
        new_record->insertField("936", subfields);
}


void MarcFormatHandler::CreateCreatorFields(const std::shared_ptr<const JSON::JSONNode> creators_node, MARC::Record * const marc_record) {
    const std::shared_ptr<const JSON::ArrayNode> creators_array(JSON::JSONNode::CastToArrayNodeOrDie("creators", creators_node));
    for (auto creator_node : *creators_array) {
        const std::shared_ptr<const JSON::ObjectNode> creator_object(JSON::JSONNode::CastToObjectNodeOrDie("creator",
                                                                                                           creator_node));
        MARC::Subfields subfields;
        std::string tag("100");
        if (creator_node != *(creators_array->begin()))
            tag = "700";

        const std::shared_ptr<const JSON::JSONNode> last_name_node(creator_object->getNode("lastName"));
        if (last_name_node == nullptr)
            throw std::runtime_error("MarcFormatHandler::CreateCreatorFields: screator is missing a last name!");
        const std::shared_ptr<const JSON::StringNode> last_name(JSON::JSONNode::CastToStringNodeOrDie("lastName",
                                                                                                      last_name_node));
        std::string name(last_name->getValue());
        const std::shared_ptr<const JSON::JSONNode> first_name_node(creator_object->getNode("firstName"));
        if (first_name_node != nullptr) {
            const std::shared_ptr<const JSON::StringNode> first_name(JSON::JSONNode::CastToStringNodeOrDie("firstName",
                                                                                                           first_name_node));
            name += ", " + first_name->getValue();
        }
        subfields.addSubfield('a', name);

        const std::shared_ptr<const JSON::JSONNode> ppn_node(creator_object->getNode("ppn"));
        if (ppn_node != nullptr) {
            const std::shared_ptr<const JSON::StringNode> ppn_string_node(JSON::JSONNode::CastToStringNodeOrDie("ppn",
                                                                                                                ppn_node));
            subfields.addSubfield('0', "(DE-576)" + ppn_string_node->getValue());
        }

        const std::shared_ptr<const JSON::JSONNode> creator_type(creator_object->getNode("creatorType"));
        std::string creator_role;
        if (creator_type != nullptr) {
            const std::shared_ptr<const JSON::StringNode> creator_role_node(JSON::JSONNode::CastToStringNodeOrDie("creatorType",
                                                                                                                  creator_type));
            subfields.addSubfield('e', creator_role_node->getValue());
        }

        marc_record->insertField(tag, subfields);
    }
}


void InsertDOI(MARC::Record * const record, const std::string &doi) {
    record->insertField("024", { { 'a', doi }, { '2', "doi" } });
}


std::pair<unsigned, unsigned> MarcFormatHandler::processRecord(const std::shared_ptr<const JSON::ObjectNode> &object_node) {
    static RegexMatcher * const ignore_fields(RegexMatcher::RegexMatcherFactory(
        "^issue|pages|publicationTitle|volume|version|date|tags|libraryCatalog|itemVersion|accessDate|key|websiteType|ISSN|ubtue$"));
    unsigned record_count(0), previously_downloaded_count(0);
    MARC::Record new_record(MARC::Record::TypeOfRecord::LANGUAGE_MATERIAL, MARC::Record::BibliographicLevel::MONOGRAPH_OR_ITEM,
                            GetNextControlNumber());
    bool is_journal_article(false);
    std::string publication_title, issn_normalized, url, website_title;
    for (const auto &key_and_node : *object_node) {
        if (ignore_fields->matched(key_and_node.first))
            continue;

        if (key_and_node.first == "language")
            new_record.insertField("041", { { 'a',
                JSON::JSONNode::CastToStringNodeOrDie(key_and_node.first, key_and_node.second)->getValue() } });
        else if (key_and_node.first == "url") {
            CreateSubfieldFromStringNode(key_and_node, "856", 'u', &new_record);
            url = reinterpret_cast<const JSON::StringNode * const>(key_and_node.second.get())->getValue();
        } else if (key_and_node.first == "title")
            CreateSubfieldFromStringNode(key_and_node, "245", 'a', &new_record);
        else if (key_and_node.first == "abstractNote")
            CreateSubfieldFromStringNode(key_and_node, "520", 'a', &new_record, /* indicator1 = */ '3');
        else if (key_and_node.first == "date")
            CreateSubfieldFromStringNode(key_and_node, "362", 'a', &new_record, /* indicator1 = */ '0');
        else if (key_and_node.first == "DOI") {
            if (unlikely(key_and_node.second->getType() != JSON::JSONNode::STRING_NODE))
                LOG_ERROR("expected DOI node to be a string node!");
            InsertDOI(&new_record, JSON::JSONNode::CastToStringNodeOrDie(key_and_node.first, key_and_node.second)->getValue());
        } else if (key_and_node.first == "shortTitle")
            CreateSubfieldFromStringNode(key_and_node, "246", 'a', &new_record);
        else if (key_and_node.first == "creators")
            CreateCreatorFields(key_and_node.second, &new_record);
        else if (key_and_node.first == "itemType") {
            const std::string item_type(JSON::JSONNode::CastToStringNodeOrDie(key_and_node.first, key_and_node.second)->getValue());
            if (item_type == "journalArticle") {
                is_journal_article = true;
                publication_title = object_node->getOptionalStringValue("publicationTitle");
                ExtractVolumeYearIssueAndPages(*object_node, &new_record);
            } else if (item_type == "magazineArticle")
                ExtractVolumeYearIssueAndPages(*object_node, &new_record);
            else if (item_type == "webpage") {
                // just add the encoding marker
                LOG_WARNING("TODO: add proper support for webpages");
                new_record.insertField("935", { { 'c', "website" } });
            } else
                LOG_ERROR("unknown item type: \"" + item_type + "\"! JSON node dump: " + object_node->toString());
        } else if (key_and_node.first == "rights") {
            const std::string copyright(JSON::JSONNode::CastToStringNodeOrDie(key_and_node.first,
                                                                              key_and_node.second)->getValue());
            if (UrlUtil::IsValidWebUrl(copyright))
                new_record.insertField("542", { { 'u', copyright } });
            else
                new_record.insertField("542", { { 'f', copyright } });
        } else if (key_and_node.first == "journalAbbreviation")
            new_record.insertField("773", { { 'p', JSON::JSONNode::CastToStringNodeOrDie(key_and_node.first,
                                                                                         key_and_node.second)->getValue() } });
        else if (key_and_node.first == "extra") {
            // comment field, can contain anything, even DOI's (e.g. for a webpage which has no DOI field)
            const std::string extra(JSON::JSONNode::CastToStringNodeOrDie(key_and_node.first,
                                                                          key_and_node.second)->getValue());
            static RegexMatcher * const doi_matcher(RegexMatcher::RegexMatcherFactory("^DOI:\\s*([0-9a-zA-Z./]+)$"));
            if (doi_matcher->matched(extra))
                InsertDOI(&new_record, (*doi_matcher)[1]);
        } else if (key_and_node.first == "websiteTitle")
            website_title = JSON::JSONNode::CastToStringNodeOrDie(key_and_node.first, key_and_node.second)->getValue();
        else
            LOG_ERROR("unknown key \"" + key_and_node.first + "\" with node type "
                      + JSON::JSONNode::TypeToString(key_and_node.second->getType()) + "! ("
                      + key_and_node.second->toString() + "), whole record: " + object_node->toString());
    }

    std::shared_ptr<const JSON::JSONNode> custom_node(object_node->getNode("ubtue"));
    if (custom_node != nullptr) {
        const std::shared_ptr<const JSON::ObjectNode>custom_object(JSON::JSONNode::CastToObjectNodeOrDie("ubtue", custom_node));
        if (custom_object->getOptionalStringNode("ISSN_untagged"))
            issn_normalized = custom_object->getOptionalStringValue("ISSN_untagged");
        else if (custom_object->getOptionalStringNode("ISSN_online"))
            issn_normalized = custom_object->getOptionalStringValue("ISSN_online");
        else if (custom_object->getOptionalStringNode("ISSN_print"))
            issn_normalized = custom_object->getOptionalStringValue("ISSN_print");
        else
            LOG_WARNING("No ISSN found for article.");

        // physical form
        const std::string physical_form(custom_object->getOptionalStringValue("physicalForm"));
        if (not physical_form.empty()) {
            if (physical_form == "A")
                new_record.insertField("007", "tu");
            else if (physical_form == "O")
                new_record.insertField("007", "cr uuu---uuuuu");
            else
                LOG_ERROR("unhandled value of physical form: \""
                          + physical_form + "\"!");
        }

        // volume
        const std::string volume(custom_object->getOptionalStringValue("volume"));
        if (not volume.empty()) {
            const auto field_it(new_record.findTag("936"));
            if (field_it == new_record.end())
                new_record.insertField("936", { { 'v', volume } });
            else
                field_it->getSubfields().addSubfield('v', volume);
        }

        // license code
        const std::string license(custom_object->getOptionalStringValue("licenseCode"));
        if (license == "l") {
            const auto field_it(new_record.findTag("936"));
            if (field_it != new_record.end())
                field_it->getSubfields().addSubfield('z', "Kostenfrei");
        }

        // SSG numbers:
        const std::string ssg_numbers(custom_object->getOptionalStringValue("ssgNumbers"));
        if (not ssg_numbers.empty())
            new_record.addSubfield("084", 'a', ssg_numbers);
    }

    // title:
    if (not website_title.empty() and not new_record.hasTag("245"))
        new_record.insertField("245", { { 'a', website_title } });

    // keywords:
    const std::shared_ptr<const JSON::JSONNode>tags_node(object_node->getNode("tags"));
    if (tags_node != nullptr)
        ExtractKeywords(tags_node, issn_normalized, augment_params_->global_params_->maps_->ISSN_to_keyword_field_map_, &new_record);

    // Populate 773:
    if (is_journal_article) {
        const auto superior_ppn_and_title(augment_params_->global_params_->maps_->ISSN_to_superior_ppn_and_title_map_.find(issn_normalized));
        if (superior_ppn_and_title != augment_params_->global_params_->maps_->ISSN_to_superior_ppn_and_title_map_.end()) {
            std::vector<MARC::Subfield> subfields;
            if (publication_title.empty())
                publication_title = superior_ppn_and_title->second.getTitle();
            if (not publication_title.empty())
                subfields.emplace_back('a', publication_title);
            if (not issn_normalized.empty())
                subfields.emplace_back('x', issn_normalized);
            const std::string journal_ppn(superior_ppn_and_title->second.getPPN());
            if (not journal_ppn.empty())
                subfields.emplace_back('w', "(DE-576)" + journal_ppn);
            if (not subfields.empty())
                new_record.insertField("773", subfields);
        }
    }

    // language code fallback:
    if (not new_record.hasTag("041"))
        new_record.insertField("041", { { 'a', DEFAULT_SUBFIELD_CODE } });

    std::string error_message;
    if (not new_record.edit(augment_params_->marc_edit_instructions_, &error_message))
        LOG_ERROR("editing the new MARC record failed: " + error_message);

    // previously downloaded?
    const std::string checksum(MARC::CalcChecksum(new_record, /* exclude_001 = */ true));
    if (unlikely(url.empty()))
        LOG_ERROR("\"url\" has not been set!");
    time_t creation_time;

    if (not download_tracker_.hasAlreadyBeenDownloaded(url, &creation_time, &error_message, checksum)
        or not error_message.empty())
    {
        marc_writer_->write(new_record);
        download_tracker_.addOrReplace(url, checksum, /* error_message = */"");
    } else
        ++previously_downloaded_count;
    ++record_count;

    return std::make_pair(record_count, previously_downloaded_count);
}


void LoadISSNToPPNMap(std::unordered_map<std::string, PPNandTitle> * const ISSN_to_superior_ppn_map) {
    std::unique_ptr<File> input(FileUtil::OpenInputFileOrDie(ISSN_TO_PPN_MAP_PATH));
    unsigned line_no(0);
    while (not input->eof()) {
        ++line_no;

        std::string line;
        if (input->getline(&line) < 18 /* ISSN + comma + PPN + comma */)
            continue;

        const size_t FIRST_COMMA_POS(line.find_first_of(','));
        if (unlikely(FIRST_COMMA_POS == std::string::npos or FIRST_COMMA_POS == 0))
            LOG_ERROR("malformed line #" + std::to_string(line_no) + " in \"" + ISSN_TO_PPN_MAP_PATH + "\"! (1)");
        const std::string ISSN(line.substr(0, FIRST_COMMA_POS));

        const size_t SECOND_COMMA_POS(line.find_first_of(',', FIRST_COMMA_POS));
        if (unlikely(SECOND_COMMA_POS == std::string::npos or SECOND_COMMA_POS == FIRST_COMMA_POS + 1))
            LOG_ERROR("malformed line #" + std::to_string(line_no) + " in \"" + ISSN_TO_PPN_MAP_PATH + "\"! (2)");
        const std::string PPN(line.substr(FIRST_COMMA_POS + 1, SECOND_COMMA_POS - FIRST_COMMA_POS - 1));

        const std::string title(StringUtil::RightTrim(" \t", line.substr(SECOND_COMMA_POS + 1)));
        ISSN_to_superior_ppn_map->emplace(ISSN, PPNandTitle(PPN, title));
    }
}


AugmentMaps::AugmentMaps(const std::string &map_directory_path) {
    MiscUtil::LoadMapFile(map_directory_path + "language_to_language_code.map", &language_to_language_code_map_);
    MiscUtil::LoadMapFile(map_directory_path + "ISSN_to_language_code.map", &ISSN_to_language_code_map_);
    MiscUtil::LoadMapFile(map_directory_path + "ISSN_to_licence.map", &ISSN_to_licence_map_);
    MiscUtil::LoadMapFile(map_directory_path + "ISSN_to_keyword_field.map", &ISSN_to_keyword_field_map_);
    MiscUtil::LoadMapFile(map_directory_path + "ISSN_to_physical_form.map", &ISSN_to_physical_form_map_);
    MiscUtil::LoadMapFile(map_directory_path + "ISSN_to_volume.map", &ISSN_to_volume_map_);
    MiscUtil::LoadMapFile(map_directory_path + "ISSN_to_SSG.map", &ISSN_to_SSG_map_);
    LoadISSNToPPNMap(&ISSN_to_superior_ppn_and_title_map_);
}


// If "key" is in "map", then return the mapped value, o/w return "key".
inline std::string OptionalMap(const std::string &key, const std::unordered_map<std::string, std::string> &map) {
    const auto &key_and_value(map.find(key));
    return (key_and_value == map.cend()) ? key : key_and_value->second;
}


// "author" must be in the lastname,firstname format. Returns the empty string if no PPN was found.
std::string DownloadAuthorPPN(const std::string &author) {
    static RegexMatcher * const matcher(RegexMatcher::RegexMatcherFactory(
         "<SMALL>PPN</SMALL>.*<div><SMALL>([0-9X]+)"));
    const std::string lookup_url("http://swb.bsz-bw.de/DB=2.104/SET=70/TTL=1/CMD?SGE=&ACT=SRCHM&MATCFILTER=Y"
                                 "&MATCSET=Y&NOSCAN=Y&PARSE_MNEMONICS=N&PARSE_OPWORDS=N&PARSE_OLDSETS=N&IMPLAND=Y"
                                 "&NOABS=Y&ACT0=SRCHA&SHRTST=50&IKT0=1&TRM0=" + UrlUtil::UrlEncode(author)
                                 +"&ACT1=*&IKT1=2057&TRM1=*&ACT2=*&IKT2=8977&TRM2=theolog*&ACT3=-&IKT3=8978-&TRM3=1"
                                 "[1%2C2%2C3%2C4%2C5%2C6%2C7%2C8][0%2C1%2C2%2C3%2C4%2C5%2C6%2C7%2C8%2C9]"
                                 "[0%2C1%2C2%2C3%2C4%2C5%2C6%2C7%2C8%2C9]?");
    Downloader downloader(lookup_url);
    if (downloader.anErrorOccurred())
        LOG_ERROR(downloader.getLastErrorMessage());
    else if (matcher->matched(downloader.getMessageBody()))
        return (*matcher)[1];
    return "";
}


void AugmentJsonCreators(const std::shared_ptr<JSON::ArrayNode> creators_array, std::vector<std::string> * const comments) {
    for (size_t i(0); i < creators_array->size(); ++i) {
        const std::shared_ptr<JSON::ObjectNode> creator_object(creators_array->getObjectNode(i));

        const std::shared_ptr<const JSON::JSONNode> last_name_node(creator_object->getNode("lastName"));
        if (last_name_node != nullptr) {
            std::string name(creator_object->getStringValue("lastName"));

            const std::shared_ptr<const JSON::JSONNode> first_name_node(creator_object->getNode("firstName"));
            if (first_name_node != nullptr)
                name += ", " + creator_object->getStringValue("firstName");

            const std::string PPN(DownloadAuthorPPN(name));
            if (not PPN.empty()) {
                comments->emplace_back("Added author PPN " + PPN + " for author " + name);
                creator_object->insert("ppn", std::make_shared<JSON::StringNode>(PPN));
            }
        }
    }
}


/* Improve JSON result delivered by Zotero Translation Server
 * Note on ISSN's: Some pages might contain multiple ISSN's (for each publication medium and/or a linking ISSN).
 *                In such cases, the Zotero translator must return tags to distinguish between them.
 */
void AugmentJson(const std::shared_ptr<JSON::ObjectNode> &object_node, const SiteAugmentParams &augment_params) {
    LOG_INFO("Augmenting JSON...");
    std::map<std::string, std::string> custom_fields;
    std::vector<std::string> comments;
    std::string issn_raw, issn_normalized;
    std::shared_ptr<JSON::StringNode> language_node(nullptr);
    for (auto &key_and_node : *object_node) {
        if (key_and_node.first == "language") {
            language_node = JSON::JSONNode::CastToStringNodeOrDie("language", key_and_node.second);
            const std::string language_json(language_node->getValue());
            const std::string language_mapped(OptionalMap(language_json,
                                                          augment_params.global_params_->maps_->language_to_language_code_map_));
            if (language_json != language_mapped) {
                language_node->setValue(language_mapped);
                comments.emplace_back("changed \"language\" from \"" + language_json + "\" to \"" + language_mapped + "\"");
            }
        } else if (key_and_node.first == "creators") {
            std::shared_ptr<JSON::ArrayNode> creators_array(JSON::JSONNode::CastToArrayNodeOrDie("creators", key_and_node.second));
            AugmentJsonCreators(creators_array, &comments);
        } else if (key_and_node.first == "ISSN") {
            if (not augment_params.parent_ISSN_online_.empty() or
                not augment_params.parent_ISSN_print_.empty()) {
                continue;   // we'll just use the override
            }
            issn_raw = JSON::JSONNode::CastToStringNodeOrDie(key_and_node.first, key_and_node.second)->getValue();
            if (unlikely(not MiscUtil::NormaliseISSN(issn_raw, &issn_normalized))) {
                // the raw ISSN string probably contains multiple ISSN's that can't be distinguished
                throw std::runtime_error("\"" + issn_raw + "\" is invalid (multiple ISSN's?)!");
            } else
                custom_fields.emplace(std::pair<std::string, std::string>("ISSN_untagged", issn_normalized));
        } else if (key_and_node.first == "date") {
            const std::string date_raw(JSON::JSONNode::CastToStringNodeOrDie(key_and_node.first, key_and_node.second)->getValue());
            custom_fields.emplace(std::pair<std::string, std::string>("date_raw", date_raw));
            struct tm tm(TimeUtil::StringToStructTm(date_raw, augment_params.strptime_format_));
            std::string date_normalized(std::to_string(tm.tm_year + 1900) + "-" + StringUtil::ToString(tm.tm_mon + 1, 10, 2, '0') + "-"
                                        + StringUtil::ToString(tm.tm_mday, 10, 2, '0'));
            custom_fields.emplace(std::pair<std::string, std::string>("date_normalized", date_normalized));
            comments.emplace_back("normalized date to: " + date_normalized);
        }
    }

    // use ISSN specified in the config file if any
    if (not augment_params.parent_ISSN_online_.empty()) {
        issn_normalized = augment_params.parent_ISSN_online_;
        custom_fields.emplace(std::pair<std::string, std::string>("ISSN_online", issn_normalized));
        LOG_DEBUG("Using default online ISSN \"" + issn_normalized + "\"");
    } else if (not augment_params.parent_ISSN_print_.empty()) {
        issn_normalized = augment_params.parent_ISSN_print_;
        custom_fields.emplace(std::pair<std::string, std::string>("ISSN_print", issn_normalized));
        LOG_DEBUG("Using default print ISSN \"" + issn_normalized + "\"");
    }

    // ISSN specific overrides
    if (not issn_normalized.empty()) {
        const auto ISSN_parent_ppn_and_title(
            augment_params.global_params_->maps_->ISSN_to_superior_ppn_and_title_map_.find(issn_normalized));
        if (ISSN_parent_ppn_and_title != augment_params.global_params_->maps_->ISSN_to_superior_ppn_and_title_map_.cend())
            custom_fields.emplace(std::pair<std::string, std::string>("PPN", ISSN_parent_ppn_and_title->second.getPPN()));

        // physical form
        const auto ISSN_and_physical_form(augment_params.global_params_->maps_->ISSN_to_physical_form_map_.find(issn_normalized));
        if (ISSN_and_physical_form != augment_params.global_params_->maps_->ISSN_to_physical_form_map_.cend()) {
            if (ISSN_and_physical_form->second == "A")
                custom_fields.emplace(std::pair<std::string, std::string>("physicalForm", "A"));
            else if (ISSN_and_physical_form->second == "O")
                custom_fields.emplace(std::pair<std::string, std::string>("physicalForm", "O"));
            else
                LOG_ERROR("unhandled entry in physical form map: \"" + ISSN_and_physical_form->second + "\"!");
        }

        // language
        const auto ISSN_and_language(augment_params.global_params_->maps_->ISSN_to_language_code_map_.find(issn_normalized));
        if (ISSN_and_language != augment_params.global_params_->maps_->ISSN_to_language_code_map_.cend()) {
            if (language_node != nullptr) {
                const std::string language_old(language_node->getValue());
                language_node->setValue(ISSN_and_language->second);
                comments.emplace_back("changed \"language\" from \"" + language_old + "\" to \"" + ISSN_and_language->second
                                      + "\" due to ISSN map");
            } else {
                language_node = std::make_shared<JSON::StringNode>(ISSN_and_language->second);
                object_node->insert("language", language_node);
                comments.emplace_back("added \"language\" \"" + ISSN_and_language->second + "\" due to ISSN map");
            }
        }

        // volume
        const std::string volume(object_node->getOptionalStringValue("volume"));
        if (volume.empty()) {
            const auto ISSN_and_volume(augment_params.global_params_->maps_->ISSN_to_volume_map_.find(issn_normalized));
            if (ISSN_and_volume != augment_params.global_params_->maps_->ISSN_to_volume_map_.cend()) {
                if (volume.empty()) {
                    const std::shared_ptr<JSON::JSONNode> volume_node(object_node->getNode("volume"));
                    JSON::JSONNode::CastToStringNodeOrDie("volume", volume_node)->setValue(ISSN_and_volume->second);
                } else {
                    std::shared_ptr<JSON::StringNode> volume_node(new JSON::StringNode(ISSN_and_volume->second));
                    object_node->insert("volume", volume_node);
                }
            }
        }

        // license code
        const auto ISSN_and_license_code(augment_params.global_params_->maps_->ISSN_to_licence_map_.find(issn_normalized));
        if (ISSN_and_license_code != augment_params.global_params_->maps_->ISSN_to_licence_map_.end()) {
            if (ISSN_and_license_code->second != "l")
                LOG_ERROR("ISSN_to_licence.map contains an ISSN that has not been mapped to an \"l\" but \""
                          + ISSN_and_license_code->second
                          + "\" instead and we don't know what to do with it!");
            else
                custom_fields.emplace(std::pair<std::string, std::string>("licenseCode", ISSN_and_license_code->second));
        }

        // SSG numbers:
        const auto ISSN_and_SSGN_numbers(augment_params.global_params_->maps_->ISSN_to_SSG_map_.find(issn_normalized));
        if (ISSN_and_SSGN_numbers != augment_params.global_params_->maps_->ISSN_to_SSG_map_.end())
            custom_fields.emplace(std::pair<std::string, std::string>("ssgNumbers", ISSN_and_SSGN_numbers->second));
    } else
        LOG_WARNING("No suitable ISSN was found!");

    // Insert custom node with fields and comments
    if (comments.size() > 0 or custom_fields.size() > 0) {
        std::shared_ptr<JSON::ObjectNode> custom_object(new JSON::ObjectNode);
        if (comments.size() > 0) {
            std::shared_ptr<JSON::ArrayNode> comments_node(new JSON::ArrayNode);
            for (const auto &comment : comments) {
                std::shared_ptr<JSON::StringNode> comment_node(new JSON::StringNode(comment));
                comments_node->push_back(comment_node);
            }
            custom_object->insert("comments", comments_node);
        }

        for (const auto &custom_field : custom_fields) {
            std::shared_ptr<JSON::StringNode> custom_field_node(new JSON::StringNode(custom_field.second));
            custom_object->insert(custom_field.first, custom_field_node);
        }

        object_node->insert("ubtue", custom_object);
    }
}


const std::shared_ptr<RegexMatcher> LoadSupportedURLsRegex(const std::string &map_directory_path) {
    std::unique_ptr<File> input(FileUtil::OpenInputFileOrDie(map_directory_path + "targets.regex"));

    std::string combined_regex;
    while (not input->eof()) {
        std::string line(input->getline());
        StringUtil::Trim(&line);
        if (likely(not line.empty())) {
            if (likely(not combined_regex.empty()))
                combined_regex += '|';
            combined_regex += "(?:" + line + ")";
        }
    }

    std::string err_msg;
    std::shared_ptr<RegexMatcher> supported_urls_regex(RegexMatcher::RegexMatcherFactory(combined_regex, &err_msg));
    if (supported_urls_regex == nullptr)
        LOG_ERROR("compilation of the combined regex failed: " + err_msg);

    return supported_urls_regex;
}


std::pair<unsigned, unsigned> Harvest(const std::string &harvest_url, const std::shared_ptr<HarvestParams> harvest_params,
                                      const SiteAugmentParams &augment_params, const std::string &harvested_html, bool log)
{
    if (harvest_url.empty())
        LOG_ERROR("empty URL passed to Zotero::Harvest");

    std::pair<unsigned, unsigned> record_count_and_previously_downloaded_count;
    static std::unordered_set<std::string> already_harvested_urls;
    if (already_harvested_urls.find(harvest_url) != already_harvested_urls.end()) {
        LOG_INFO("Skipping URL (already harvested): " + harvest_url);
        return record_count_and_previously_downloaded_count;
    }
    already_harvested_urls.emplace(harvest_url);

    LOG_INFO("Harvesting URL: " + harvest_url);

    std::string response_body, error_message;
    unsigned response_code;
    harvest_params->min_url_processing_time_.sleepUntilExpired();
    Downloader::Params downloader_params;
    downloader_params.user_agent_ = harvest_params->user_agent_;
    const bool download_succeeded(TranslationServer::Web(harvest_params->zts_server_url_, /* time_limit = */ DEFAULT_TIMEOUT,
                                                         downloader_params, Url(harvest_url), &response_body, &response_code,
                                                         &error_message, harvested_html));

    harvest_params->min_url_processing_time_.restart();
    if (not download_succeeded) {
        LOG_WARNING("Zotero conversion failed: " + error_message);
        return std::make_pair(0, 0);
    }

    std::shared_ptr<JSON::JSONNode> tree_root(nullptr);
    JSON::Parser json_parser(response_body);
    if (not (json_parser.parse(&tree_root)))
        LOG_ERROR("failed to parse returned JSON: " + json_parser.getErrorMessage() + "\n" + response_body);

    // 300 => multiple matches found, try to harvest children
    if (response_code == 300) {
        LOG_INFO("multiple articles found => trying to harvest children");
        if (tree_root->getType() == JSON::ArrayNode::OBJECT_NODE) {
            const std::shared_ptr<const JSON::ObjectNode>object_node(JSON::JSONNode::CastToObjectNodeOrDie("tree_root",
                                                                                                           tree_root));

            for (const auto &key_and_node : *object_node) {
                std::string key_and_node_url(key_and_node.first);
                if (MiscUtil::IsDOI(key_and_node_url))
                    key_and_node_url = "https://doi.org/" + key_and_node_url;

                std::pair<unsigned, unsigned> record_count_and_previously_downloaded_count2 =
                    Harvest(key_and_node_url, harvest_params, augment_params, /* harvested_html = */"", /* log = */false);

                record_count_and_previously_downloaded_count.first += record_count_and_previously_downloaded_count2.first;
                record_count_and_previously_downloaded_count.second += record_count_and_previously_downloaded_count2.second;
            }
        }
    } else {
        const std::shared_ptr<const JSON::ArrayNode>json_array(JSON::JSONNode::CastToArrayNodeOrDie("tree_root", tree_root));
        for (const auto entry : *json_array) {
            const std::shared_ptr<JSON::ObjectNode> json_object(JSON::JSONNode::CastToObjectNodeOrDie("entry", entry));
            try {
                AugmentJson(json_object, augment_params);
                record_count_and_previously_downloaded_count = harvest_params->format_handler_->processRecord(json_object);
            } catch (const std::exception &x) {
                LOG_WARNING("Couldn't process record! Error: " + std::string(x.what()));
                return record_count_and_previously_downloaded_count;
            }
        }
    }
    ++harvest_params->harvested_url_count_;

    if (log) {
        LOG_INFO("Harvested " + StringUtil::ToString(record_count_and_previously_downloaded_count.first) + " record(s) from "
                 + harvest_url + '\n' + "of which "
                 + StringUtil::ToString(record_count_and_previously_downloaded_count.first
                                        - record_count_and_previously_downloaded_count.second)
                 + " records were new records.");
    }
    return record_count_and_previously_downloaded_count;
}


const std::string DownloadTracker::DEFAULT_ZOTERO_DOWNLOADS_DB_PATH("/usr/local/var/lib/tuelib/zotero_downloads.db");


DownloadTracker::DownloadTracker(const std::string &previous_downloads_db_path) {
    if (not db_.open(previous_downloads_db_path.c_str(),
                     kyotocabinet::HashDB::OREADER | kyotocabinet::HashDB::OWRITER | kyotocabinet::HashDB::OCREATE
                     | kyotocabinet::HashDB::OAUTOTRAN | kyotocabinet::HashDB::OAUTOSYNC))
        LOG_ERROR("Failed to open or create the KyotoCabinet database \"" + previous_downloads_db_path + "\" ("
                  + std::string(db_.error().message()) + ")!");
}


inline static void SplitTimestampErrorMessageAndHash(const std::string &raw_value, time_t * const creation_time,
                                                     std::string * const error_message, std::string * const hash)
{
    if (unlikely(raw_value.size() <= sizeof(time_t)))
        LOG_ERROR("raw value is too small!");
    *creation_time = *reinterpret_cast<const time_t * const>(raw_value.data());
    *error_message = raw_value.substr(sizeof(time_t)).c_str();
    *hash = raw_value.substr(sizeof(time_t) + error_message->length() + 1 /* for the terminating NUL */);
}


bool DownloadTracker::hasAlreadyBeenDownloaded(const std::string &url, time_t * const creation_time,
                                                       std::string * const error_message, const std::string &hash) const
{
    std::string value;
    if (not db_.get(url, &value))
        return false;

    if (hash.empty())
        return true;

    std::string stored_hash;
    SplitTimestampErrorMessageAndHash(value, creation_time, error_message, &stored_hash);
    return hash == stored_hash;
}


void DownloadTracker::addOrReplace(const std::string &url, const std::string &hash, const std::string &error_message) {
    if (unlikely((hash.empty() and error_message.empty()) or (not hash.empty() and not error_message.empty())))
        LOG_ERROR("exactly one of \"hash\" and \"error_message\" must be non-empty!");

    const time_t now(std::time(nullptr));
    const std::string timestamp(reinterpret_cast<const char * const>(&now), sizeof(now));
    if (unlikely(not db_.set(url, timestamp + std::string(1, '\0') + hash)))
        LOG_ERROR("failed to insert a value into \"" + getPath() + "\":" + std::string(db_.error().message()));
}


size_t DownloadTracker::listMatches(const std::string &url_regex, std::vector<Entry> * const entries) const {
    std::unique_ptr<RegexMatcher> matcher(RegexMatcher::RegexMatcherFactoryOrDie(url_regex));

    entries->clear();

    std::unique_ptr<kyotocabinet::DB::Cursor> cursor(db_.cursor());
    if (unlikely(cursor == nullptr))
        LOG_ERROR("failed to create a cursor for \"" + getPath() + "\":" + std::string(db_.error().message()));
    if (not cursor->jump())
        LOG_ERROR("failed to position a cursor at the first record for \"" + getPath() + "\":" + std::string(db_.error().message()));

    std::string url, value;
    while (cursor->get(&url, &value, true /* = move the cursor to the next record */)) {
        if (matcher->matched(url)) {
            time_t creation_time;
            std::string error_message, hash;
            SplitTimestampErrorMessageAndHash(value, &creation_time, &error_message, &hash);
            entries->emplace_back(url, creation_time, error_message, hash);
        }
    }

    return entries->size();
}


// Helper function for DownloadTracker::deleteMatches and DownloadTracker::deleteOldEntries.
template<typename Predicate> static size_t DeleteEntries(kyotocabinet::HashDB * const db, const std::string &db_path,
                                                         const Predicate &deletion_predicate)
{
    std::unique_ptr<kyotocabinet::DB::Cursor> cursor(db->cursor());
    if (unlikely(cursor == nullptr))
        LOG_ERROR("failed to create a cursor for \"" + db_path + "\":" + std::string(db->error().message()));
    if (not cursor->jump())
        LOG_ERROR("failed to position a cursor at the first record for \"" + db_path + "\":" + std::string(db->error().message()));

    size_t deleted_count(0);
    std::string url, value;
    while (cursor->get(&url, &value, true /* = move the cursor to the next record */)) {
        time_t creation_time;
        std::string hash, error_message;
        SplitTimestampErrorMessageAndHash(value, &creation_time, &error_message, &hash);
        if (deletion_predicate(url, creation_time)) {
            if (unlikely(not db->remove(url)))
                LOG_ERROR("can't remove entry with key \"" + url + "\" from \"" + db_path + "\"! (This should *never* happen!");
            ++deleted_count;
        }
    }

    return deleted_count;
}


size_t DownloadTracker::deleteMatches(const std::string &url_regex) {
    std::shared_ptr<RegexMatcher> matcher(RegexMatcher::RegexMatcherFactoryOrDie(url_regex));

    return DeleteEntries(&db_, getPath(),
                         [matcher](const std::string &url, const time_t /*creation_timestamp*/){ return matcher->matched(url); });
}


size_t DownloadTracker::deleteSingleEntry(const std::string &url) {
    return db_.remove(url) ? 1 : 0;
}


size_t DownloadTracker::deleteOldEntries(const time_t cutoff_timestamp) {
    return DeleteEntries(&db_, getPath(),
                         [cutoff_timestamp](const std::string &/*url*/, const time_t creation_timestamp)
                             { return creation_timestamp <= cutoff_timestamp; });
}


size_t DownloadTracker::size() const {
    const int64_t no_of_db_entries(db_.count());
    if (unlikely(no_of_db_entries == -1))
        LOG_ERROR("unable to determine the number of entries in the database \"" + getPath() + "\"!");

    return static_cast<size_t>(no_of_db_entries);
}


UnsignedPair HarvestSite(const SimpleCrawler::SiteDesc &site_desc, const SimpleCrawler::Params &crawler_params,
                         const std::shared_ptr<RegexMatcher> &supported_urls_regex,
                         const std::shared_ptr<HarvestParams> &harvest_params, const SiteAugmentParams &augment_params,
                         File * const progress_file)
{
    UnsignedPair total_record_count_and_previously_downloaded_record_count;
    LOG_INFO("Starting crawl at base URL: " +  site_desc.start_url_);
    SimpleCrawler crawler(site_desc, crawler_params);
    SimpleCrawler::PageDetails page_details;
    unsigned processed_url_count(0);
    while (crawler.getNextPage(&page_details)) {
        if (not supported_urls_regex->matched(page_details.url_))
            LOG_INFO("Skipping unsupported URL: " + page_details.url_);
        else if (page_details.error_message_.empty()) {
            const auto record_count_and_previously_downloaded_count(
                Harvest(page_details.url_, harvest_params, augment_params, page_details.body_));
            total_record_count_and_previously_downloaded_record_count.first  += record_count_and_previously_downloaded_count.first;
            total_record_count_and_previously_downloaded_record_count.second += record_count_and_previously_downloaded_count.second;
            if (progress_file != nullptr) {
                progress_file->rewind();
                if (unlikely(not progress_file->write(
                    std::to_string(processed_url_count) + ";" + std::to_string(crawler.getRemainingCallDepth()) + ";" + page_details.url_)))
                    LOG_ERROR("failed to write progress to \"" + progress_file->getPath());
            }
        }
    }

    return total_record_count_and_previously_downloaded_record_count;
}


UnsignedPair HarvestURL(const std::string &url, const std::shared_ptr<HarvestParams> &harvest_params,
                        const SiteAugmentParams &augment_params)
{
    return Harvest(url, harvest_params, augment_params, "");
}


namespace {


// Returns true if we can determine that the last_build_date column value stored in the rss_feeds table for the feed identified
// by "feed_url" is no older than the "last_build_date" time_t passed into this function.  (This is somewhat complicated by the
// fact that both, the column value as well as the time_t value may contain indeterminate values.)
bool FeedContainsNoNewItems(const RSSHarvestMode mode, DbConnection * const db_connection, const std::string &feed_url,
                            const time_t last_build_date)
{
    db_connection->queryOrDie("SELECT last_build_date FROM rss_feeds WHERE feed_url='" + db_connection->escapeString(feed_url)
                              + "'");
    DbResultSet result_set(db_connection->getLastResultSet());

    std::string date_string;
    if (result_set.empty()) {
        if (last_build_date == TimeUtil::BAD_TIME_T)
            date_string = SqlUtil::DATETIME_RANGE_MIN;
        else
            date_string = SqlUtil::TimeTToDatetime(last_build_date);

        if (mode == RSSHarvestMode::VERBOSE)
            LOG_INFO("Creating new feed entry in rss_feeds table for \"" + feed_url + "\".");
        if (mode != RSSHarvestMode::TEST)
            db_connection->queryOrDie("INSERT INTO rss_feeds SET feed_url='" + db_connection->escapeString(feed_url)
                                      + "',last_build_date='" + date_string + "'");
        return false;
    }

    const DbRow first_row(result_set.getNextRow());
    date_string = first_row["last_build_date"];
    if (date_string != SqlUtil::DATETIME_RANGE_MIN and last_build_date != TimeUtil::BAD_TIME_T
        and SqlUtil::DatetimeToTimeT(date_string) >= last_build_date)
        return true;

    return false;
}


// Returns the feed ID for the URL "feed_url".
std::string GetFeedID(const RSSHarvestMode mode, DbConnection * const db_connection, const std::string &feed_url) {
    db_connection->queryOrDie("SELECT id FROM rss_feeds WHERE feed_url='" + db_connection->escapeString(feed_url)
                              + "'");
    DbResultSet result_set(db_connection->getLastResultSet());
    if (unlikely(result_set.empty())) {
        if (mode == RSSHarvestMode::TEST)
            return "-1"; // Must be an INT.
        LOG_ERROR("unexpected missing feed for URL \"" + feed_url + "\".");
    }
    const DbRow first_row(result_set.getNextRow());
    return first_row["id"];
}


// Returns true if the item with item ID "item_id" and feed ID "feed_id" were found in the rss_items table, else
// returns false.
bool ItemAlreadyProcessed(DbConnection * const db_connection, const std::string &feed_id, const std::string &item_id) {
    db_connection->queryOrDie("SELECT creation_datetime FROM rss_items WHERE feed_id='"
                              + feed_id + "' AND item_id='" + db_connection->escapeString(item_id) + "'");
    DbResultSet result_set(db_connection->getLastResultSet());
    if (result_set.empty())
        return false;

    if (logger->getMinimumLogLevel() >= Logger::LL_DEBUG) {
        const DbRow first_row(result_set.getNextRow());
        LOG_DEBUG("Previously retrieved item w/ ID \"" + item_id + "\" at " + first_row["creation_datetime"] + ".");
    }

    return true;
}


void UpdateLastBuildDate(DbConnection * const db_connection, const std::string &feed_url, const time_t last_build_date) {
    std::string last_build_date_string;
    if (last_build_date == TimeUtil::BAD_TIME_T)
        last_build_date_string = SqlUtil::DATETIME_RANGE_MIN;
    else
        last_build_date_string = SqlUtil::TimeTToDatetime(last_build_date);
    db_connection->queryOrDie("UPDATE rss_feeds SET last_build_date='" + last_build_date_string + "' WHERE feed_url='"
                              + db_connection->escapeString(feed_url) + "'");
}


} // unnamed namespace


UnsignedPair HarvestSyndicationURL(const RSSHarvestMode mode, const std::string &feed_url,
                                   const std::shared_ptr<HarvestParams> &harvest_params,
                                   const SiteAugmentParams &augment_params, DbConnection * const db_connection)
{
    UnsignedPair total_record_count_and_previously_downloaded_record_count;

    if (mode != RSSHarvestMode::NORMAL)
        LOG_INFO("Processing URL: " + feed_url);

    Downloader::Params downloader_params;
    downloader_params.user_agent_ = harvest_params->user_agent_;
    Downloader downloader(feed_url, downloader_params);
    if (downloader.anErrorOccurred()) {
        LOG_WARNING("Download problem for \"" + feed_url + "\": " + downloader.getLastErrorMessage());
        return total_record_count_and_previously_downloaded_record_count;
    }

    SyndicationFormat::AugmentParams syndication_format_augment_params;
    syndication_format_augment_params.strptime_format_ = augment_params.strptime_format_;
    std::string err_msg;
    std::unique_ptr<SyndicationFormat> syndication_format(
        SyndicationFormat::Factory(downloader.getMessageBody(), syndication_format_augment_params, &err_msg));
    if (syndication_format == nullptr) {
        LOG_WARNING("Problem parsing XML document for \"" + feed_url + "\": " + err_msg);
        return total_record_count_and_previously_downloaded_record_count;
    }

    const time_t last_build_date(syndication_format->getLastBuildDate());
    if (mode != RSSHarvestMode::NORMAL) {
        std::cout << feed_url << " (" << syndication_format->getFormatName() << "):\n";
        std::cout << "\tTitle: " << syndication_format->getTitle() << '\n';
        if (last_build_date != TimeUtil::BAD_TIME_T)
            std::cout << "\tLast build date: " << TimeUtil::TimeTToUtcString(last_build_date) << '\n';
        std::cout << "\tLink: " << syndication_format->getLink() << '\n';
        std::cout << "\tDescription: " << syndication_format->getDescription() << '\n';
   }

    if (mode != RSSHarvestMode::TEST and FeedContainsNoNewItems(mode, db_connection, feed_url, last_build_date))
        return total_record_count_and_previously_downloaded_record_count;

    const std::string feed_id(mode == RSSHarvestMode::TEST ? "" : GetFeedID(mode, db_connection, feed_url));
    for (const auto &item : *syndication_format) {
        if (mode != RSSHarvestMode::TEST and ItemAlreadyProcessed(db_connection, feed_id, item.getId()))
            continue;

        const std::string title(item.getTitle());
        if (not title.empty() and mode != RSSHarvestMode::NORMAL)
            LOG_INFO("\t\tTitle: " + title);

        const auto record_count_and_previously_downloaded_count(
            Harvest(item.getLink(), harvest_params, augment_params, "", /* verbose = */ mode != RSSHarvestMode::NORMAL));
        total_record_count_and_previously_downloaded_record_count += record_count_and_previously_downloaded_count;

        if (mode != RSSHarvestMode::TEST)
            db_connection->queryOrDie("INSERT INTO rss_items SET feed_id='" + feed_id + "',item_id='"
                                      + db_connection->escapeString(item.getId()) + "'");

    }
    if (mode != RSSHarvestMode::TEST)
        UpdateLastBuildDate(db_connection, feed_url, last_build_date);

    return total_record_count_and_previously_downloaded_record_count;
}


} // namespace Zotero
