/** \brief Utility for flagging PPNs that may need to be augmented with bible references.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
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

#include <iostream>
#include <stdexcept>
#include <unordered_map>
#include <vector>
#include <cstdlib>
#include "BibleUtil.h"
#include "FileUtil.h"
#include "MARC.h"
#include "RegexMatcher.h"
#include "StringUtil.h"
#include "TextUtil.h"
#include "util.h"


namespace {


void Usage() __attribute__((noreturn));


void Usage() {
    std::cerr << "Usage: " << ::progname << " marc_input ppn_candidate_list\n";
    std::exit(EXIT_FAILURE);
}


void LoadPericopes(std::unordered_map<std::string, std::string> * const pericopes_to_codes_map) {
    const std::string PERIOCPES_FILE("/usr/local/var/lib/tuelib/bibleRef/pericopes_to_codes.map");
    std::unique_ptr<File> input(FileUtil::OpenInputFileOrDie(PERIOCPES_FILE));
    unsigned pericope_count(0), line_no(0);
    while (not input->eof()) {
        ++line_no;
        std::string line;
        input->getline(&line);
        StringUtil::TrimWhite(&line);
        if (unlikely(line.empty()))
            continue;
        ++pericope_count;
        const auto last_equal_pos(line.rfind('='));
        if (unlikely(last_equal_pos == std::string::npos))
            logger->error("in LoadPericopes: line # " + std::to_string(line_no) + " in \"" + PERIOCPES_FILE
                          + "\" does not contain an equal sign!");
        (*pericopes_to_codes_map)[line.substr(0, last_equal_pos)] = line.substr(last_equal_pos + 1);
    }

    std::cout << "Loaded " << pericope_count << " pericopes.\n";
}


bool HasBibleReference(const MARC::Record &record) {
    return record.getFirstField(BibleUtil::BIB_REF_RANGE_TAG) != record.end();
}


std::string NormaliseTitle(std::string title) {
    TextUtil::UTF8ToLower(&title);
    return TextUtil::CollapseWhitespace(title);
}


std::string GetPericope(const std::string &normalised_title,
                        const std::unordered_map<std::string, std::string> &pericopes_to_codes_map)
{
    for (const auto &pericope_and_codes : pericopes_to_codes_map) {
        if (normalised_title.find(pericope_and_codes.first) != std::string::npos)
            return pericope_and_codes.first;
    }

    return "";
}


std::string GetPossibleBibleReference(const std::string &normalised_title,
                                      const BibleUtil::BibleBookCanoniser &bible_book_canoniser,
                                      const BibleUtil::BibleBookToCodeMapper &bible_book_to_code_mapper)
{
    // Regex taken from https://stackoverflow.com/questions/22254746/bible-verse-regex
    static RegexMatcher * const matcher(RegexMatcher::RegexMatcherFactory(
        "(\\d*)\\s*([a-z]+)\\s*(\\d+)(:(\\d+))?(\\s*-\\s*(\\d+)(\\s*([a-z]+)\\s*(\\d+))?(:(\\d+))?)?"));
    if (not matcher->matched(normalised_title))
        return "";

    const std::string bible_reference_candidate((*matcher)[0]);
    std::string book_candidate, chapters_and_verses_candidate;
    BibleUtil::SplitIntoBookAndChaptersAndVerses(bible_reference_candidate, &book_candidate, &chapters_and_verses_candidate);

    book_candidate = bible_book_canoniser.canonise(book_candidate, /* verbose = */false);
    const std::string book_code(bible_book_to_code_mapper.mapToCode(book_candidate, /* verbose = */false));
    if (book_code.empty())
        return "";

    std::set<std::pair<std::string, std::string>> start_end;
    return BibleUtil::ParseBibleReference(chapters_and_verses_candidate, book_code, &start_end) ? bible_reference_candidate : "";
}


void ProcessRecords(MARC::Reader * const marc_reader, File * const ppn_candidate_list,
                    const std::unordered_map<std::string, std::string> &pericopes_to_codes_map,
                    const BibleUtil::BibleBookCanoniser &bible_book_canoniser,
                    const BibleUtil::BibleBookToCodeMapper &bible_book_to_code_mapper)
{
    unsigned record_count(0), ppn_candidate_count(0);
    while (const MARC::Record record = marc_reader->read()) {
        ++record_count;

        if (HasBibleReference(record))
            continue;

        const std::string PPN(record.getControlNumber());
        const auto title_field(record.getFirstField("245"));
        if (unlikely(title_field == record.end()))
            logger->error("record w/ PPN " + PPN + " is missing a title field!");

        const MARC::Subfields _245_subfields(title_field->getSubfields());
        const std::string title(_245_subfields.getFirstSubfieldWithCode('a'));
        if (unlikely(title.empty())) {
            logger->warning("record w/ PPN " + record.getControlNumber() + " is missing a title subfield!");
            continue;
        }

        const std::string normalised_title(NormaliseTitle(title));
        std::string bib_ref_candidate(GetPericope(normalised_title, pericopes_to_codes_map));
        if (bib_ref_candidate.empty())
            bib_ref_candidate = GetPossibleBibleReference(normalised_title, bible_book_canoniser,
                                                          bible_book_to_code_mapper);
        StringUtil::TrimWhite(&bib_ref_candidate);
        if (not bib_ref_candidate.empty()) {
            ++ppn_candidate_count;
            ppn_candidate_list->write("\"" + PPN + "\",\"" + TextUtil::CSVEscape(bib_ref_candidate) + "\",\""
                                      + TextUtil::CSVEscape("https://ixtheo.de/Record/" + PPN) + "\"\n");
        }
    }

    std::cout << "Processed " << record_count << " MARC bibliographic record(s).\n";
    std::cout << "Found " << ppn_candidate_count << " record(s) that may need a bible reference.\n";
}


} // unnamed namespace


int main(int argc, char *argv[]) {
    ::progname = argv[0];

    if (argc != 3)
        Usage();

    std::unique_ptr<MARC::Reader> marc_reader(MARC::Reader::Factory(argv[1]));
    std::unique_ptr<File> ppn_candidate_list(FileUtil::OpenOutputFileOrDie(argv[2]));

    try {
        const BibleUtil::BibleBookCanoniser bible_book_canoniser(
            "/usr/local/var/lib/tuelib/bibleRef/books_of_the_bible_to_canonical_form.map");
        const BibleUtil::BibleBookToCodeMapper bible_book_to_code_mapper(
            "/usr/local/var/lib/tuelib/bibleRef/books_of_the_bible_to_code.map");

        std::unordered_map<std::string, std::string> pericopes_to_codes_map;
        LoadPericopes(&pericopes_to_codes_map);

        ProcessRecords(marc_reader.get(), ppn_candidate_list.get(), pericopes_to_codes_map, bible_book_canoniser,
                       bible_book_to_code_mapper);
    } catch (const std::exception &e) {
        logger->error("Caught exception: " + std::string(e.what()));
    }
}
