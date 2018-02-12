/** \file   SmartDownloader.cc
 *  \brief  Implementation of descedants of the SmartDownloader class.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2015,2017,2018 Universitätsbiblothek Tübingen.  All rights reserved.
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
#include "SmartDownloader.h"
#include <iostream>
#include "Downloader.h"
#include "FileUtil.h"
#include "IdbPager.h"
#include "MediaTypeUtil.h"
#include "RegexMatcher.h"
#include "StringUtil.h"
#include "util.h"


namespace {


bool DownloadHelper(const std::string &url, const TimeLimit &time_limit,
                    std::string * const document, std::string * const http_header_charset,
                    std::string * const error_message)
{
    Downloader downloader(url, Downloader::Params(), time_limit);
    if (downloader.anErrorOccurred()) {
        *error_message = downloader.getLastErrorMessage();
        return false;
    }

    *document = downloader.getMessageBody();
    *http_header_charset = downloader.getCharset();
    return true;
}


} // unnamed namespace


SmartDownloader::SmartDownloader(const std::string &regex, const bool trace): trace_(trace) {
    std::string err_msg;
    matcher_.reset(RegexMatcher::RegexMatcherFactory(regex, &err_msg));
    if (not matcher_)
        ERROR("pattern failed to compile \"" + regex + "\"!");
}


bool SmartDownloader::canHandleThis(const std::string &url) const {
    std::string err_msg;
    if (matcher_->matched(url, &err_msg)) {
        if (not err_msg.empty())
            ERROR("an error occurred while trying to match \"" + url + "\" with \""
                  + matcher_->getPattern() + "\"! (" + err_msg + ")");

        return true;
    }

    return false;
}


bool SmartDownloader::downloadDoc(const std::string &url, const TimeLimit &time_limit, std::string * const document,
                                  std::string * const http_header_charset, std::string * const error_message)
{
    if (downloadDocImpl(url, time_limit, document, http_header_charset, error_message)) {
        ++success_count_;
        return true;
    } else
        return false;
}


bool DSpaceDownloader::canHandleThis(const std::string &url) const {
    return url.find("dspace") != std::string::npos;
}


bool DSpaceDownloader::downloadDocImpl(const std::string &url, const TimeLimit &time_limit,
                                       std::string * const document, std::string * const http_header_charset,
                                       std::string * const error_message)
{
    document->clear();

    std::string html_document_candidate;
    if (not DownloadHelper(url, time_limit, &html_document_candidate, http_header_charset, error_message))
        return false;

    static RegexMatcher *matcher;
    if (matcher == nullptr) {
        std::string err_msg;
        matcher = RegexMatcher::RegexMatcherFactory("meta content=\"http(.*)pdf\"", &err_msg);
        if (matcher == nullptr)
            ERROR("failed to compile regex! (" + err_msg + ")");
    }

    if (not matcher->matched(html_document_candidate))
        return false;

    const std::string pdf_link("http" + (*matcher)[1] + "pdf");
    if (not DownloadHelper(pdf_link, time_limit, &html_document_candidate, http_header_charset, error_message))
        return false;

    return true;
}


bool SimpleSuffixDownloader::canHandleThis(const std::string &url) const {
    for (const auto &suffix : suffixes_) {
        if (StringUtil::IsProperSuffixOfIgnoreCase(suffix, url))
            return true;
    }

    return false;
}


bool SimpleSuffixDownloader::downloadDocImpl(const std::string &url, const TimeLimit &time_limit,
                                             std::string * const document, std::string * const http_header_charset,
                                             std::string * const error_message)
{
    if (trace_)
        INFO("about to download \"" + url + "\".");
    return (DownloadHelper(url, time_limit, document, http_header_charset, error_message));
}


bool SimplePrefixDownloader::canHandleThis(const std::string &url) const {
    for (const auto &prefix : prefixes_) {
        if (StringUtil::StartsWith(url, prefix, /* ignore_case = */ true))
            return true;
    }

    return false;
}


bool SimplePrefixDownloader::downloadDocImpl(const std::string &url, const TimeLimit &time_limit,
                                             std::string * const document, std::string * const http_header_charset,
                                             std::string * const error_message)
{
    if (trace_)
        INFO("about to download \"" + url + "\".");
    return (DownloadHelper(url, time_limit, document, http_header_charset, error_message));
}


bool DigiToolSmartDownloader::downloadDocImpl(const std::string &url, const TimeLimit &time_limit,
                                              std::string * const document, std::string * const http_header_charset,
                                              std::string * const error_message)
{
    static RegexMatcher * const matcher(
        RegexMatcher::RegexMatcherFactory("http://digitool.hbz-nrw.de:1801/webclient/DeliveryManager\\?pid=\\d+"));

    std::string err_msg;
    size_t start_pos, end_pos;
    if (not matcher->matched(url, &err_msg, &start_pos, &end_pos))
        ERROR("match failed: " + err_msg);

    const std::string normalised_url(url.substr(start_pos, end_pos - start_pos));

    if (trace_)
        INFO("about to download \"" + url + "\".");
    if (not DownloadHelper(normalised_url, time_limit, document, http_header_charset, error_message) or time_limit.limitExceeded())
        return false;

    static const std::string ocr_text("ocr-text:\n");
    if (MediaTypeUtil::GetMediaType(*document) == "text/plain"
        and StringUtil::StartsWith(*document, ocr_text))
        *document = StringUtil::ISO8859_15ToUTF8(document->substr(ocr_text.length()));

    return true;
}


bool DiglitSmartDownloader::downloadDocImpl(const std::string &url, const TimeLimit &time_limit,
                                            std::string * const document, std::string * const http_header_charset,
                                            std::string * const error_message)
{
    if (trace_)
        INFO("about to download \"" + url + "\".");
    if (not DownloadHelper(url, time_limit, document, http_header_charset, error_message)) {
        if (trace_)
            WARNING("original download failed!");
        return false;
    }
    const std::string start_string("<input type=\"hidden\" name=\"projectname\" value=\"");
    size_t start_pos(document->find(start_string));
    if  (start_pos == std::string::npos) {
        if (trace_)
            WARNING("start position not found!");
        return false;
    }
    start_pos += start_string.length();
    const size_t end_pos(document->find('"', start_pos));
    if  (end_pos == std::string::npos) {
        if (trace_)
            WARNING("end position not found!");
        return false;
    }
    const std::string projectname(document->substr(start_pos, end_pos - start_pos));
    document->clear();
    std::string page;

    RomanPageNumberGenerator roman_page_number_generator;
    IdbPager roman_pager(projectname, &roman_page_number_generator);
    while (roman_pager.getNextPage(time_limit, &page)) {
        if (time_limit.limitExceeded()) {
            if (trace_)
                WARNING("time out while paging! (roman numbers)");
            return false;
        }
        document->append(page);
    }

    ArabicPageNumberGenerator arabic_page_number_generator;
    IdbPager arabic_pager(projectname, &arabic_page_number_generator);
    while (arabic_pager.getNextPage(time_limit, &page)) {
        if (time_limit.limitExceeded()) {
            if (trace_)
                WARNING("time out while paging! (arabic numbers)");
            return false;
        }
        document->append(page);
    }

    return not document->empty();
}


bool BszSmartDownloader::downloadDocImpl(const std::string &url, const TimeLimit &time_limit,
                                         std::string * const document, std::string * const http_header_charset,
                                         std::string * const error_message)
{
    const std::string doc_url(url.substr(0, url.size() - 3) + "pdf");
    if (trace_)
        INFO("about to download \"" + doc_url + "\".");
    return DownloadHelper(url, time_limit, document, http_header_charset, error_message);
}


bool BvbrSmartDownloader::downloadDocImpl(const std::string &url, const TimeLimit &time_limit,
                                          std::string * const document, std::string * const http_header_charset,
                                          std::string * const error_message)
{
    std::string html;
    if (trace_)
        INFO("about to download \"" + url + "\".");
    if (not DownloadHelper(url, time_limit, document, http_header_charset, error_message) or time_limit.limitExceeded())
        return false;
    const std::string start_string("<body onload=window.location=\"");
    size_t start_pos(html.find(start_string));
    if (start_pos == std::string::npos)
        return false;
    start_pos += start_string.size();
    const size_t end_pos(html.find('"', start_pos + 1));
    if (end_pos == std::string::npos)
        return false;
    const std::string doc_url("http://bvbr.bib-bvb.de:8991" + html.substr(start_pos, end_pos - start_pos));
    if (trace_)
        INFO("about to download \"" + doc_url + "\".");
    return DownloadHelper(url, time_limit, document, http_header_charset, error_message);
}


bool Bsz21SmartDownloader::downloadDocImpl(const std::string &url, const TimeLimit &time_limit,
                                           std::string * const document, std::string * const http_header_charset,
                                           std::string * const error_message)
{
    if (trace_)
        INFO("about to download \"" + url + "\".");
    if (not DownloadHelper(url, time_limit, document, http_header_charset, error_message) or time_limit.limitExceeded())
        return false;
    if (MediaTypeUtil::GetMediaType(*document) == "application/pdf")
        return true;

    std::string start_string("Persistente URL: <a id=\"pers_url\" href=\"");
    size_t start_pos(document->find(start_string));
    std::string doc_url;
    if (start_pos != std::string::npos) {
        start_pos += start_string.size();
        const size_t end_pos(document->find('"', start_pos + 1));
        if (end_pos == std::string::npos)
            return false;
        const std::string pers_url(document->substr(start_pos, end_pos - start_pos));
        const size_t last_slash_pos(pers_url.rfind('/'));
        if (last_slash_pos == std::string::npos or last_slash_pos == pers_url.size() - 1)
            return false;
        doc_url = "http://idb.ub.uni-tuebingen.de/cgi-bin/digi-downloadPdf.fcgi?projectname="
                  + pers_url.substr(last_slash_pos + 1);
    } else {
        start_pos = document->find("name=\"citation_pdf_url\"");
        if (start_pos == std::string::npos)
            return true;
        start_string = "meta content=\"";
        start_pos = document->rfind(start_string, start_pos);
        if (start_pos == std::string::npos)
            return false;
        start_pos += start_string.size();
        const size_t end_pos(document->find('"', start_pos + 1));
        if (end_pos == std::string::npos)
            return false;
        doc_url = document->substr(start_pos, end_pos - start_pos);
    }

    if (trace_)
        INFO("about to download \"" + doc_url + "\".");
    return DownloadHelper(url, time_limit, document, http_header_charset, error_message);
}


bool LocGovSmartDownloader::downloadDocImpl(const std::string &url, const TimeLimit &time_limit,
                                            std::string * const document, std::string * const http_header_charset,
                                            std::string * const error_message)
{
    if (url.length() < 11)
        return false;
    const std::string doc_url("http://catdir" + url.substr(10));
    std::string html;
    if (trace_)
        INFO("about to download \"" + doc_url + "\".");
    const int retcode = DownloadHelper(url, time_limit, &html, http_header_charset, error_message);

    if (retcode != 0)
        return false;
    size_t toc_start_pos(StringUtil::FindCaseInsensitive(html, "<TITLE>Table of contents"));
    if (toc_start_pos == std::string::npos)
        return false;
    const size_t pre_start_pos(StringUtil::FindCaseInsensitive(html, "<pre>"));
    if (pre_start_pos == std::string::npos)
        return false;
    const size_t pre_end_pos(StringUtil::FindCaseInsensitive(html, "</pre>"));
    if (pre_end_pos == std::string::npos)
        return false;
    *document = html.substr(pre_start_pos + 5, pre_end_pos - pre_start_pos - 5);
    return true;
}


bool DefaultDownloader::downloadDocImpl(const std::string &url, const TimeLimit &time_limit,
                                        std::string * const document, std::string * const http_header_charset,
                                        std::string * const error_message)
{
    return DownloadHelper(url, time_limit, document, http_header_charset, error_message);
}


bool SmartDownload(const std::string &url, const TimeLimit &time_limit, std::string * const document,
                   std::string * const http_header_charset, std::string * const error_message,
                   const bool trace)
{
    document->clear();

    static std::vector<SmartDownloader *> smart_downloaders{
        new DSpaceDownloader(trace),
        new SimpleSuffixDownloader({ ".pdf", ".jpg", ".jpeg", ".txt" }, trace),
        new SimplePrefixDownloader({ "http://www.bsz-bw.de/cgi-bin/ekz.cgi?" }, trace),
        new SimplePrefixDownloader({ "http://deposit.d-nb.de/cgi-bin/dokserv?" }, trace),
        new SimplePrefixDownloader({ "http://media.obvsg.at/" }, trace),
        new SimplePrefixDownloader({ "http://d-nb.info/" }, trace),
        new DigiToolSmartDownloader(trace),
        new DiglitSmartDownloader(trace),
        new BszSmartDownloader(trace),
        new BvbrSmartDownloader(trace),
        new Bsz21SmartDownloader(trace),
        new LocGovSmartDownloader(trace),
        new DefaultDownloader(trace)
    };

    for (auto &smart_downloader : smart_downloaders) {
        if (smart_downloader->canHandleThis(url))
            return smart_downloader->downloadDoc(url, time_limit, document, http_header_charset, error_message);
    }

    return false;
}
