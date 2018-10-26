/** \file   SmartDownloader.cc
 *  \brief  Implementation of descedants of the SmartDownloader class.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2015,2017,2018 Universitätsbibliothek Tübingen.  All rights reserved.
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
        LOG_ERROR("pattern failed to compile \"" + regex + "\"!");
}


bool SmartDownloader::canHandleThis(const std::string &url) const {
    std::string err_msg;
    if (matcher_->matched(url, &err_msg)) {
        if (not err_msg.empty())
            LOG_ERROR("an error occurred while trying to match \"" + url + "\" with \""
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

    if (not DownloadHelper(url, time_limit, document, http_header_charset, error_message))
        return false;

    static RegexMatcher *matcher;
    if (matcher == nullptr) {
        std::string err_msg;
        matcher = RegexMatcher::RegexMatcherFactory("meta content=\"http(.*)pdf\"", &err_msg);
        if (matcher == nullptr)
            LOG_ERROR("failed to compile regex! (" + err_msg + ")");
    }

    if (not matcher->matched(*document)) {
        *error_message = "no matching DSpace structure found!";
        return false;
    }

    const std::string pdf_link("http" + (*matcher)[1] + "pdf");
    if (not DownloadHelper(pdf_link, time_limit, document, http_header_charset, error_message))
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
        LOG_INFO("about to download \"" + url + "\".");
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
        LOG_INFO("about to download \"" + url + "\".");
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
        LOG_ERROR("match failed: " + err_msg);

    const std::string normalised_url(url.substr(start_pos, end_pos - start_pos));

    if (trace_)
        LOG_INFO("about to download \"" + url + "\".");
    if (not DownloadHelper(normalised_url, time_limit, document, http_header_charset, error_message))
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
    std::string url_improved(url);
    if (RegexMatcher::Matched("/diglit/", url))
        url_improved = StringUtil::ReplaceString("/diglit/", "/opendigi/", &url_improved);
    if (RegexMatcher::Matched("/opendigi/", url_improved))
        url_improved = url_improved + "/ocr";

    if (trace_ and url != url_improved)
        LOG_INFO("converted url \"" + url + "\" to \"" + url_improved + "\"");

    if (trace_)
        LOG_INFO("about to download \"" + url_improved + "\".");
    if (not DownloadHelper(url_improved, time_limit, document, http_header_charset, error_message)) {
        if (trace_)
            LOG_WARNING("original download failed!");
        return false;
    }

    return not document->empty();
}


bool BszSmartDownloader::downloadDocImpl(const std::string &url, const TimeLimit &time_limit,
                                         std::string * const document, std::string * const http_header_charset,
                                         std::string * const error_message)
{
    const std::string doc_url(url.substr(0, url.size() - 3) + "pdf");
    if (trace_)
        LOG_INFO("about to download \"" + doc_url + "\".");
    return DownloadHelper(url, time_limit, document, http_header_charset, error_message);
}


bool BvbrSmartDownloader::downloadDocImpl(const std::string &url, const TimeLimit &time_limit,
                                          std::string * const document, std::string * const http_header_charset,
                                          std::string * const error_message)
{
    if (trace_)
        LOG_INFO("about to download \"" + url + "\".");
    if (not DownloadHelper(url, time_limit, document, http_header_charset, error_message))
        return false;
    const std::string start_string("<body onload=window.location=\"");
    size_t start_pos(document->find(start_string));
    if (start_pos == std::string::npos) {
        *error_message = "no matching Bvbr structure found!";
        return false;
    }
    start_pos += start_string.size();
    const size_t end_pos(document->find('"', start_pos + 1));
    if (end_pos == std::string::npos) {
        *error_message = "no matching Bvbr structure found! (part 2)";
        return false;
    }
    const std::string doc_url("http://bvbr.bib-bvb.de:8991" + document->substr(start_pos, end_pos - start_pos));
    if (trace_)
        LOG_INFO("about to download \"" + doc_url + "\".");
    return DownloadHelper(doc_url, time_limit, document, http_header_charset, error_message);
}


bool Bsz21SmartDownloader::downloadDocImpl(const std::string &url, const TimeLimit &time_limit,
                                           std::string * const document, std::string * const http_header_charset,
                                           std::string * const error_message)
{
    if (trace_)
        LOG_INFO("about to download \"" + url + "\".");
    if (not DownloadHelper(url, time_limit, document, http_header_charset, error_message))
        return false;

    if (MediaTypeUtil::GetMediaType(*document) == "application/pdf")
        return true;

    std::string start_string("Persistente URL: <a id=\"pers_url\" href=\"");
    size_t start_pos(document->find(start_string));
    std::string doc_url;
    if (start_pos != std::string::npos) {
        start_pos += start_string.size();
        const size_t end_pos(document->find('"', start_pos + 1));
        if (end_pos == std::string::npos) {
            *error_message = "no matching Bsz2l structure found! (part 1)";
            return false;
        }
        const std::string pers_url(document->substr(start_pos, end_pos - start_pos));
        const size_t last_slash_pos(pers_url.rfind('/'));
        if (last_slash_pos == std::string::npos or last_slash_pos == pers_url.size() - 1) {
            *error_message = "no matching Bsz2l structure found! (part 2)";
            return false;
        }
        doc_url = "http://idb.ub.uni-tuebingen.de/cgi-bin/digi-downloadPdf.fcgi?projectname="
                  + pers_url.substr(last_slash_pos + 1);
    } else {
        start_pos = document->find("name=\"citation_pdf_url\"");
        if (start_pos == std::string::npos)
            return true;
        start_string = "meta content=\"";
        start_pos = document->rfind(start_string, start_pos);
        if (start_pos == std::string::npos) {
            *error_message = "no matching Bsz2l structure found! (part 3)";
            return false;
        }
        start_pos += start_string.size();
        const size_t end_pos(document->find('"', start_pos + 1));
        if (end_pos == std::string::npos) {
            *error_message = "no matching Bsz2l structure found! (part 4)";
            return false;
        }
        doc_url = document->substr(start_pos, end_pos - start_pos);
    }

    if (trace_)
        LOG_INFO("about to download \"" + doc_url + "\".");
    return DownloadHelper(url, time_limit, document, http_header_charset, error_message);
}


bool LocGovSmartDownloader::downloadDocImpl(const std::string &url, const TimeLimit &time_limit,
                                            std::string * const document, std::string * const http_header_charset,
                                            std::string * const error_message)
{
    if (url.length() < 11) {
        *error_message = "LocGov URL too short!";
        return false;
    }
    const std::string doc_url("http://catdir" + url.substr(10));
    if (trace_)
        LOG_INFO("about to download \"" + doc_url + "\".");

    return DownloadHelper(doc_url, time_limit, document, http_header_charset, error_message);
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
        if (smart_downloader->canHandleThis(url)) {
            LOG_DEBUG("Downloading url " + url + " using " + smart_downloader->getName());
            return smart_downloader->downloadDoc(url, time_limit, document, http_header_charset, error_message);
        }
    }

    *error_message = "No downloader available for URL: " + url;
    return false;
}
