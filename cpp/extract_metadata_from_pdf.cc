/** \brief Tool extracting metadata if only a PDF fulltext is available
 *  \author Johannes Riedl
 *
 *  \copyright 2018,2019 Universitätsbibliothek Tübingen.  All rights reserved.
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

#include <iostream>
#include <stdexcept>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include "FileUtil.h"
#include "FullTextImport.h"
#include "PdfUtil.h"
#include "RegexMatcher.h"
#include "Solr.h"
#include "SolrJSON.h"
#include "StringUtil.h"
#include "util.h"

// Try to derive relevant information to guess the PPN
// Strategy 1: Try to find an ISBN string
// Strategy 2: Extract pages at the beginning and try to identify information at
//             the bottom of the first page and try to guess author and title


namespace {

const std::string solr_host_and_port("localhost:8080");

[[noreturn]] void Usage() {
    std::cerr << "Usage: " << ::progname << " [--min-log-level=min_verbosity] pdf_input full_text_output\n\n";
    std::exit(EXIT_FAILURE);
}

std::string GuessISSN(const std::string first_page_text, std::string * const issn) {
    std::string first_page_text_trimmed(first_page_text);
    StringUtil::Trim(&first_page_text_trimmed, '\n');
    std::size_t last_paragraph_start(first_page_text_trimmed.rfind("\n\n"));
    std::string last_paragraph(last_paragraph_start != std::string::npos ?
                                first_page_text_trimmed.substr(last_paragraph_start) : "");
    StringUtil::Map(&last_paragraph, '\n', ' ');
    static RegexMatcher * const matcher(RegexMatcher::RegexMatcherFactory(".*ISSN\\s*([\\d\\-X]+).*"));
    if (matcher->matched(last_paragraph))
        *issn = (*matcher)[1];
    return last_paragraph;
}


void GuessISBN(const std::string extracted_text, std::string * const isbn) {
     static RegexMatcher * const matcher(RegexMatcher::RegexMatcherFactory(".*ISBN\\s*([\\d\\-X]+).*"));
     if (matcher->matched(extracted_text))
         *isbn = (*matcher)[1];
}


void GuessAuthorAndTitle(const std::string &pdf_document, FullTextImport::FullTextData * const fulltext_data) {
    std::string pdfinfo_output;
    PdfUtil::ExtractPDFInfo(pdf_document, &pdfinfo_output);
    static RegexMatcher * const authors_matcher(RegexMatcher::RegexMatcherFactory("Author:\\s*(.*)", nullptr, RegexMatcher::CASE_INSENSITIVE));
    if (authors_matcher->matched(pdfinfo_output)) {
        StringUtil::Split((*authors_matcher)[1], std::set<char>({';','|'}), &(fulltext_data->authors_));
    }
    static RegexMatcher * const title_matcher(RegexMatcher::RegexMatcherFactory("^Title:?\\s*(.*)", nullptr, RegexMatcher::CASE_INSENSITIVE));
    if (title_matcher->matched(pdfinfo_output)) {
        fulltext_data->title_ = (*title_matcher)[1];
    }
}


void GetFulltextMetadataFromSolr(const std::string control_number, FullTextImport::FullTextData * const fulltext_data) {
    std::string json_result;
    std::string err_msg;
    const std::string query(std::string("id:") + control_number);
    if (unlikely(not Solr::Query(query, "id,title,author,author2,publishDate", &json_result, &err_msg,
                                 solr_host_and_port,/* timeout */ 5, Solr::JSON)))
        LOG_ERROR("Solr query failed or timed-out: \"" + query + "\". (" + err_msg + ")");
    std::shared_ptr<const JSON::ArrayNode> docs;
    SolrJSON::ParseTreeAndGetDocs(json_result, docs);
    if (docs->size() != 1)
        LOG_ERROR("Invalid size " + std::to_string(docs->size()) + " for SOLR results");
    const std::shared_ptr<const JSON::ObjectNode> doc_obj(JSON::JSONNode::CastToObjectNodeOrDie("document object", *(docs->begin())));
    fulltext_data->title_ = SolrJSON::GetTitle(doc_obj);
    const auto authors(SolrJSON::GetAuthors(doc_obj));
    fulltext_data->authors_.insert(std::begin(authors), std::end(authors));
    fulltext_data->year_ = SolrJSON::GetFirstPublishDate(doc_obj);
}


bool GuessPDFMetadata(const std::string &pdf_document, FullTextImport::FullTextData * const fulltext_data) {
    ControlNumberGuesser control_number_guesser;
    std::set<std::string> control_numbers;
    // Try to find an ISBN in the first pages
    std::string first_pages_text;
    PdfUtil::ExtractText(pdf_document, &first_pages_text, "1", "10" );
    std::string isbn;
    GuessISBN(first_pages_text, &isbn);
    if (not isbn.empty()) {
        LOG_INFO("Extracted ISBN: " + isbn);
        control_number_guesser.lookupISBN(isbn, &control_numbers);
        if (control_numbers.size() != 1)
            LOG_ERROR("We got more than one control number for ISBN \"" + isbn + "\"");
        const std::string control_number(*(control_numbers.begin()));
        LOG_INFO("Determined control number \"" + control_number + "\" for ISBN \"" + isbn + "\"\n");
        GetFulltextMetadataFromSolr(control_number, fulltext_data);
        return true;
    }

    // Guess control number by author, title and and possibly issn
    std::string first_page_text;
    PdfUtil::ExtractText(pdf_document, &first_page_text, "1", "1" ); // Get only first page
    std::string issn;
    const std::string last_paragraph(GuessISSN(first_page_text, &issn));
    fulltext_data->issn_ = issn;
    GuessAuthorAndTitle(pdf_document, fulltext_data);
    std::string control_number;
    if (unlikely(not FullTextImport::CorrelateFullTextData(control_number_guesser, *(fulltext_data), &control_number)))
        return false;
    return true;
}


bool ExtractFulltext(const std::string &pdf_document, FullTextImport::FullTextData * const fulltext_data) {
     return PdfUtil::ExtractText(pdf_document, &(fulltext_data->full_text_));
}


} // unnamed namespace


int Main(int argc, char *argv[]) {
    if (argc < 3)
        Usage();

    FullTextImport::FullTextData fulltext_data;
    const std::string fulltext_location(argv[1]);
    std::string pdf_document;
    if (not FileUtil::ReadString(fulltext_location, &pdf_document))
        LOG_ERROR("Could not read \"" + fulltext_location + "\"");
    if (PdfUtil::PdfDocContainsNoText(pdf_document))
        LOG_ERROR("Apparently no text in \"" + fulltext_location + "\"");
    if (unlikely(not GuessPDFMetadata(pdf_document, &fulltext_data)))
        LOG_ERROR("Unable to determine metadata for \"" +  fulltext_location + "\"");
    if (unlikely(not ExtractFulltext(pdf_document, &fulltext_data)))
        LOG_ERROR("Unable to extract fulltext from \"" + fulltext_location + "\"");
    auto plain_text_output(FileUtil::OpenOutputFileOrDie(argv[2]));
    FullTextImport::WriteExtractedTextToDisk(fulltext_data.full_text_, fulltext_data.title_, fulltext_data.authors_, fulltext_data.doi_,
                                             fulltext_data.year_, fulltext_data.issn_, fulltext_data.isbn_, plain_text_output.get());


    return EXIT_SUCCESS;
}


