/** \file    full_text_cache_monitor.cc
 *  \brief   A CGI-tool to execute Zotero RSS & Crawling mechanisms
 *  \author  Mario Trojan
 */
/*
    Copyright (C) 2016-2018, Library of the University of Tübingen

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

#include <algorithm>
#include <iostream>
#include <string>
#include <vector>
#include <sys/types.h>
#include <sys/wait.h>
#include "ExecUtil.h"
#include "FileUtil.h"
#include "IniFile.h"
#include "StringUtil.h"
#include "Template.h"
#include "TextUtil.h"
#include "TimeUtil.h"
#include "WallClockTimer.h"
#include "WebUtil.h"
#include "util.h"


namespace {


std::string zts_client_maps_directory;
std::string zts_url;
enum HarvestType { RSS, CRAWLING };
const std::map<std::string, int> STRING_TO_HARVEST_TYPE_MAP = { { "RSS", static_cast<int>(RSS) },
                                                                { "CRAWL", static_cast<HarvestType>(CRAWLING) } };
const std::string TEMPLATE_DIRECTORY("/usr/local/var/lib/tuelib/zotero_cgi/");
const std::string CRAWLER_EXAMPLE_FILE("/usr/local/ub_tools/cpp/data/zotero_crawler.conf");
const std::string ZTS_HARVESTER_CONF_FILE("/usr/local/ub_tools/cpp/data/zts_harvester.conf");
const std::vector<std::pair<std::string,std::string>> OUTPUT_FORMAT_IDS_AND_EXTENSIONS = {
    // custom formats
    { "marcxml", "xml" },
    { "marc21", "mrc" },
    { "json", "json" },

    // native zotero formats, see https://github.com/zotero/translation-server/blob/master/src/server_translation.js#L31-43
    { "bibtex", "bibtex" },
    { "biblatex", "biblatex" },
    { "bookmarks", "bookmarks" },
    { "coins", "coins" },
    { "csljson", "csljson" },
    { "mods", "mods" },
    { "refer", "refer" },
    { "rdf_bibliontology", "rdf_bib" },
    { "rdf_dc", "rdf_dc" },
    { "rdf_zotero", "rdf_zotero" },
    { "ris", "ris" },
    { "tei", "tei" },
    { "wikipedia", "wikipedia" }
};
std::multimap<std::string, std::string> cgi_args;


std::string GetCGIParameterOrDefault(const std::string &parameter_name, const std::string &default_value = "") {
    const auto key_and_value(cgi_args.find(parameter_name));
    if (key_and_value == cgi_args.cend())
        return default_value;

    return key_and_value->second;
}


std::string GetMinElementOrDefault(const std::vector<std::string> &elements, const std::string &default_value = "") {
    const auto min_element(std::min_element(elements.begin(), elements.end(), [](const std::string &a, const std::string &b){ return a < b; }));
    if (unlikely(min_element == elements.end()))
        return default_value;

    return *min_element;
}


void ParseConfigFile(Template::Map * const names_to_values_map) {
    IniFile ini(ZTS_HARVESTER_CONF_FILE);

    std::vector<std::string> all_journal_titles;
    std::vector<std::string> all_journal_issns;
    std::vector<std::string> all_journal_methods;
    std::vector<std::string> all_urls;

    std::vector<std::string> rss_journal_titles;
    std::vector<std::string> rss_journal_issns;
    std::vector<std::string> rss_feed_urls;

    std::vector<std::string> crawling_journal_titles;
    std::vector<std::string> crawling_journal_issns;
    std::vector<std::string> crawling_base_urls;
    std::vector<std::string> crawling_extraction_regexes;
    std::vector<std::string> crawling_depths;

    for (const auto &name_and_section : ini) {
        auto section(name_and_section.second);
        std::string title(section.getSectionName());

        if (title.empty()) {
            zts_url = section.getString("zts_server_url");
            zts_client_maps_directory = section.getString("map_directory_path");
        } else {
            const HarvestType harvest_type(static_cast<HarvestType>(section.getEnum("type", STRING_TO_HARVEST_TYPE_MAP)));
            const std::string harvest_type_raw(section.getString("type"));
            const std::string issn(section.getString("issn"));

            all_journal_titles.emplace_back(title);
            all_journal_issns.emplace_back(issn);
            all_journal_methods.emplace_back(harvest_type_raw);

            if (harvest_type == RSS) {
                all_urls.emplace_back(section.getString("feed"));

                rss_journal_titles.emplace_back(title);
                rss_journal_issns.emplace_back(issn);
                rss_feed_urls.emplace_back(section.getString("feed"));
            } else if (harvest_type == CRAWLING) {
                all_urls.emplace_back(section.getString("base_url"));

                crawling_journal_titles.emplace_back(title);
                crawling_journal_issns.emplace_back(issn);
                crawling_base_urls.emplace_back(section.getString("base_url"));
                crawling_extraction_regexes.emplace_back(section.getString("extraction_regex"));
                crawling_depths.emplace_back(section.getString("max_crawl_depth"));
            }
        }
    }

    if (zts_url.empty())
        LOG_ERROR("Zotero Translation Server Url not defined in config file!");
    if (zts_client_maps_directory.empty())
        LOG_ERROR("Zotero Mapping Directory not defined in config file!");

    names_to_values_map->insertArray("all_journal_titles", all_journal_titles);
    names_to_values_map->insertArray("all_journal_issns", all_journal_issns);
    names_to_values_map->insertArray("all_journal_methods", all_journal_methods);
    names_to_values_map->insertArray("all_urls", all_urls);

    names_to_values_map->insertArray("rss_journal_titles", rss_journal_titles);
    names_to_values_map->insertArray("rss_journal_issns", rss_journal_issns);
    names_to_values_map->insertArray("rss_feed_urls", rss_feed_urls);

    names_to_values_map->insertArray("crawling_journal_titles", crawling_journal_titles);
    names_to_values_map->insertArray("crawling_journal_issns", crawling_journal_issns);
    names_to_values_map->insertArray("crawling_base_urls", crawling_base_urls);
    names_to_values_map->insertArray("crawling_extraction_regexes", crawling_extraction_regexes);
    names_to_values_map->insertArray("crawling_depths", crawling_depths);

    const std::string first_crawling_journal_title(GetMinElementOrDefault(crawling_journal_titles));
    names_to_values_map->insertScalar("selected_crawling_journal_title", GetCGIParameterOrDefault("crawling_journal_title", first_crawling_journal_title));
    const std::string first_rss_journal_title(GetMinElementOrDefault(rss_journal_titles));
    names_to_values_map->insertScalar("selected_rss_journal_title", GetCGIParameterOrDefault("rss_journal_title", first_rss_journal_title));
}


std::vector<std::string> GetOutputFormatIds() {
    std::vector<std::string> output_formats;

    for (const auto &output_format_id_and_extension : OUTPUT_FORMAT_IDS_AND_EXTENSIONS)
        output_formats.push_back(output_format_id_and_extension.first);

    return output_formats;
}


std::string GetOutputFormatExtension(const std::string &output_format_id) {
    for (const auto &output_format_id_and_extension : OUTPUT_FORMAT_IDS_AND_EXTENSIONS) {
        if (output_format_id_and_extension.first == output_format_id)
            return output_format_id_and_extension.second;
    }
    LOG_ERROR("no extension defined for output format " + output_format_id);
}


std::string BuildCommandString(const std::string &command, const std::vector<std::string> &args) {
    std::string command_string(command);

    for (const std::string &arg : args)
        command_string += " \"" + arg + "\"";

    return command_string;
}


std::string PrepareMapsDirectory(const std::string &orig_directory, const std::string &tmp_directory) {
    ExecUtil::ExecOrDie(ExecUtil::Which("cp"), { "-r", orig_directory, tmp_directory });
    const std::string local_maps_directory(tmp_directory + "/zts_client_maps");
    const std::string file_prev_downloaded(local_maps_directory + "/previously_downloaded.hashes");
    FileUtil::DeleteFile(file_prev_downloaded);
    FileUtil::CreateSymlink("/dev/null", file_prev_downloaded);
    return local_maps_directory;
}


void UpdateProgress(std::string progress) {
    std::cout << "<script type=\"text/javascript\">UpdateProgress(atob('" + TextUtil::Base64Encode(progress) + "'));</script>\r\n";
    std::cout << std::flush;
}


void UpdateRuntime(unsigned seconds) {
    std::cout << "<script type=\"text/javascript\">UpdateRuntime(" + std::to_string(seconds) + ");</script>\r\n";
    std::cout << std::flush;

    fflush(stdout);
}


class CrawlingTask {
    FileUtil::AutoTempDirectory auto_temp_dir_;
    std::string executable_;
    std::string progress_path_;
    std::string command_;
    std::string out_path_;
    std::string log_path_;
    pid_t pid_;

public:
    std::string output_;
    std::string GetCommand() { return command_; }
    std::string GetOutPath() { return out_path_; }
    std::string GetLogPath() { return log_path_; }
    pid_t GetPid() { return pid_; }

    struct Progress {
        bool exists_ = false;
        unsigned processed_url_count_;
        unsigned remaining_depth_;
        std::string current_url_;
    };

    Progress GetProgress() {
        Progress progress;
        if (FileUtil::Exists(progress_path_)) {
            std::string progress_string;
            FileUtil::ReadString(progress_path_, &progress_string);
            std::vector<std::string> progress_values;
            StringUtil::SplitThenTrimWhite(progress_string, ';', &progress_values);

            // check size, file might be empty the first few attempts
            if (progress_values.size() == 3) {
                progress.exists_ = true;
                progress.processed_url_count_ = StringUtil::ToUnsigned(progress_values[0]);
                progress.remaining_depth_ = StringUtil::ToUnsigned(progress_values[1]);
                progress.current_url_ = progress_values[2];
            }
        }

        return progress;
    }
private:
    void writeConfigFile(const std::string &file_cfg, const std::string &url_base, const std::string &url_regex, const unsigned depth) {
        std::string cfg_content = "# start_URL max_crawl_depth URL_regex\n";
        cfg_content += url_base + " " + std::to_string(depth) + " " + url_regex;
        FileUtil::WriteStringOrDie(file_cfg, cfg_content);
    }

    void executeCommand(const std::string &cfg_path, const std::string &dir_maps,
                        const std::string &output_format)
    {
        progress_path_ = dir_maps + "/progress";
        std::vector<std::string> args;

        args.emplace_back("--simple-crawler-config-file=" + cfg_path);
        args.emplace_back("--progress-file=" + progress_path_);
        args.emplace_back("--output-format=" + output_format);
        args.emplace_back(zts_url);
        args.emplace_back(dir_maps);
        args.emplace_back(out_path_);

        command_ = BuildCommandString(executable_, args);
        log_path_ = dir_maps + "/log";
        pid_ = ExecUtil::Spawn(executable_, args, "",
                               log_path_,
                               log_path_);
    }
public:
    CrawlingTask(const std::string &url_base, const std::string &url_regex, const unsigned depth, const std::string &output_format)
        : auto_temp_dir_("/tmp/ZtsMap_", /*cleanup_if_exception_is_active*/ false, /*remove_when_out_of_scope*/ false),
          executable_(ExecUtil::Which("zts_client"))
    {
        const std::string local_maps_directory(PrepareMapsDirectory(zts_client_maps_directory, auto_temp_dir_.getDirectoryPath()));
        const std::string file_extension(GetOutputFormatExtension(output_format));
        out_path_ = auto_temp_dir_.getDirectoryPath() + "/output." + file_extension;
        const std::string file_cfg(auto_temp_dir_.getDirectoryPath() + "/config.cfg");

        writeConfigFile(file_cfg, url_base, url_regex, depth);
        executeCommand(file_cfg, local_maps_directory, output_format);
    }
};


class RssTask {
    FileUtil::AutoTempDirectory auto_temp_dir_;
    std::string executable_;
    std::string command_;
    int exit_code_;
    std::string out_path_;
    std::string output_;
public:
    std::string GetCommand() { return command_; }
    int GetExitCode() { return exit_code_; }
    std::string GetOutPath() { return out_path_; }
    std::string GetOutput() { return output_; }
private:
    void executeCommand(const std::string &rss_url_file, const std::string &map_dir) {
        std::vector<std::string> args;
        args.emplace_back("--test");
        args.emplace_back(rss_url_file);
        args.emplace_back(zts_url);
        args.emplace_back(map_dir);
        args.emplace_back(out_path_);

        command_ = BuildCommandString(executable_, args);
        const std::string log_path(map_dir + "/log");
        exit_code_ = ExecUtil::Exec(executable_, args, "", log_path, log_path);
        FileUtil::ReadString(log_path, &output_);
    }
public:
    RssTask(const std::string &url_rss, const std::string &output_format_id)
        : auto_temp_dir_("/tmp/ZtsMaps_", /*cleanup_if_exception_is_active*/ false, /*remove_when_out_of_scope*/ false),
          executable_(ExecUtil::Which("rss_harvester"))
    {
        const std::string local_maps_directory(PrepareMapsDirectory(zts_client_maps_directory, auto_temp_dir_.getDirectoryPath()));
        const std::string file_extension(GetOutputFormatExtension(output_format_id));
        out_path_ = auto_temp_dir_.getDirectoryPath() + "/output." + file_extension;
        const std::string file_cfg(auto_temp_dir_.getDirectoryPath() + "/config.cfg");
        FileUtil::WriteString(file_cfg, url_rss);
        executeCommand(file_cfg, local_maps_directory);
    }
};


void ProcessDownloadAction() {
    const std::string path(GetCGIParameterOrDefault("id"));

    if (StringUtil::EndsWith(path, ".xml", /*ignore_case*/ true))
        std::cout << "Content-Type: application/xml; charset=utf-8\r\n\r\n";
    else
        std::cout << "Content-Type: text/plain; charset=utf-8\r\n\r\n";

    std::cout << FileUtil::ReadStringOrDie(path);
}


void ProcessRssAction() {
    std::cout << "<h2>RSS Result</h2>\r\n";
    std::cout << "<table>\r\n";

    RssTask rss_task(GetCGIParameterOrDefault("rss_feed_url"), GetCGIParameterOrDefault("rss_output_format"));

    std::cout << "<tr><td>Command</td><td>" + rss_task.GetCommand() + "</td></tr>\r\n";

    // todo: getresult.php ersetzen
    if (rss_task.GetExitCode() == 0)
        std::cout << "<tr><td>Download</td><td><a target=\"_blank\" href=\"?action=download&id=" + rss_task.GetOutPath() + "\">Result file</a></td></tr>\r\n";
    else
        std::cout << "<tr><td>ERROR</td><td>Exitcode: " + std::to_string(rss_task.GetExitCode()) + "</td></tr>\r\n";

    // use <pre> instead of nl2br + htmlspecialchars
    std::cout << "<tr><td>CLI output:</td><td><pre>" + rss_task.GetOutput() + "</pre></td></tr>\r\n";

    std::cout << "</table>\r\n";
}


/** \brief mod_deflate needs to be disabled for this program for flush to work correctly */
void ProcessCrawlingAction() {
    std::cout << "<h2>Crawling Result</h2>\r\n";
    std::cout << "<table>\r\n";

    CrawlingTask crawling_task(GetCGIParameterOrDefault("crawling_base_url"), GetCGIParameterOrDefault("crawling_extraction_regex"),
                               StringUtil::ToUnsigned(GetCGIParameterOrDefault("crawling_depth")), GetCGIParameterOrDefault("crawling_output_format"));

    std::cout << "<tr><td>Command</td><td>" + crawling_task.GetCommand() + "</td></tr>\r\n";
    std::cout << "<tr><td>Runtime</td><td id=\"runtime\"></td></tr>\r\n";
    std::cout << "<tr><td>Progress</td><td><div id=\"progress\">Harvesting...</div></td></tr>\r\n";
    std::cout << std::flush;

    // start status monitoring
    CrawlingTask::Progress progress;
    CrawlingTask::Progress progress_old;
    WallClockTimer timer(WallClockTimer::CUMULATIVE_WITH_AUTO_START);
    int status;

    do {
        TimeUtil::Millisleep(1000);
        timer.stop();
        UpdateRuntime(static_cast<unsigned>(timer.getTime()));
        timer.start();
        progress = crawling_task.GetProgress();
        if (progress.exists_ and progress.current_url_ != progress_old.current_url_) {
            std::string progress_string("Current URL: <a target=\"_blank\" href=\"" + progress.current_url_ + "\">" + progress.current_url_ + "</a><br/>\r\n");
            progress_string += "Current Depth: " + std::to_string(StringUtil::ToUnsigned(GetCGIParameterOrDefault("crawling_depth")) - progress.remaining_depth_) + "<br/>\r\n";
            progress_string += "Processed URL count: " + std::to_string(progress.processed_url_count_) + "<br/>\r\n";
            UpdateProgress(progress_string);
            progress_old = progress;

        }
    } while (::waitpid(crawling_task.GetPid(), &status, WNOHANG) >= 0);
    timer.stop();

    int exit_code(-2);
    if WIFEXITED(status)
        exit_code = WEXITSTATUS(status);

    FileUtil::ReadString(crawling_task.GetLogPath(), &crawling_task.output_);

    if (exit_code == 0) {
        UpdateProgress("Finished");
        std::cout << "<tr><td>Download</td><td><a target=\"_blank\" href=\"?action=download&id=" + crawling_task.GetOutPath() + "\">Result file</a></td></tr>\r\n";
    } else {
        UpdateProgress("Failed");
        std::cout << "<tr><td>ERROR</td><td>Exitcode: " + std::to_string(exit_code) + "</td></tr>\r\n";
    }

    // use <pre> instead of nl2br + htmlspecialchars
    std::cout << "<tr><td>CLI output:</td><td><pre>" + crawling_task.output_ + "</td></tr>\r\n";
    std::cout << "</table>\r\n";
}


} // unnamed namespace


int main(int argc, char *argv[]) {
    ::progname = argv[0];

    try {
        WebUtil::GetAllCgiArgs(&cgi_args, argc, argv);
        const std::string action(GetCGIParameterOrDefault("action", "list"));

        if (action == "download")
            ProcessDownloadAction();
        else {
            std::cout << "Content-Type: text/html; charset=utf-8\r\n\r\n";

            Template::Map names_to_values_map;
            names_to_values_map.insertScalar("action", action);

            std::string style_css;
            FileUtil::ReadString(TEMPLATE_DIRECTORY + "style.css", &style_css);
            names_to_values_map.insertScalar("style_css", style_css);

            std::string scripts_js;
            FileUtil::ReadString(TEMPLATE_DIRECTORY + "scripts.js", &scripts_js);
            names_to_values_map.insertScalar("scripts_js", scripts_js);

            const std::string depth(GetCGIParameterOrDefault("depth", "1"));
            names_to_values_map.insertScalar("depth", depth);

            const std::string output_format_id(GetCGIParameterOrDefault("output_format_id"));
            names_to_values_map.insertScalar("output_format_id", output_format_id);
            names_to_values_map.insertArray("output_format_ids", GetOutputFormatIds());

            names_to_values_map.insertScalar("zotero_translation_server_url", zts_url);
            std::ifstream template_html(TEMPLATE_DIRECTORY + "index.html", std::ios::binary);
            ParseConfigFile(&names_to_values_map);
            Template::ExpandTemplate(template_html, std::cout, names_to_values_map);

            if (action == "rss")
                ProcessRssAction();
            else if (action == "crawling")
                ProcessCrawlingAction();

            std::cout << "</body></html>";
        }

    } catch (const std::exception &x) {
        logger->error("caught exception: " + std::string(x.what()));
    }
}
