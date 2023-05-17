/** \file    convert_de_gruyter_csv_to_marc
 *  \brief   Convert fixed CSV-Input for EZW reference work to MARC
 *  \author  Johannes Riedl
 */

/*
    Copyright (C) 2023 Library of the University of Tübingen

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

#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_set>
#include <utility>
#include <vector>
#include <cstdlib>
#include "Compiler.h"
#include "ExecUtil.h"
#include "MARC.h"
#include "StringUtil.h"
#include "TextUtil.h"
#include "TimeUtil.h"
#include "TranslationUtil.h"
#include "UBTools.h"
#include "util.h"


enum column_name {
    LANG,
    BOOKPARTID,
    URL,
    TYPE,
    TITLE,
    BOOKTITLE,
    VOL_TITLE,
    VOL,
    ISBN,
    DOI,
    PPUB,
    EPUB,
    AUTHOR1,
    AUTHOR_ETAL,
    ZIELSTICHWORT
};

const std::string PSEUDO_PPN_PREFIX("EBR");

namespace {

[[noreturn]] void Usage() {
    ::Usage("ezw.csv marc_output");
}


std::string GetPPN(const std::string &csv_ppn = "") {
    static unsigned pseudo_ppn_index(0);
    if (not csv_ppn.empty())
        return csv_ppn;

    std::ostringstream pseudo_ppn;
    pseudo_ppn << PSEUDO_PPN_PREFIX << std::setfill('0') << std::setw(7) << ++pseudo_ppn_index;
    return pseudo_ppn.str();
}


MARC::Record *CreateNewRecord(const std::string &ppn = "") {
    return new MARC::Record(MARC::Record::TypeOfRecord::LANGUAGE_MATERIAL, MARC::Record::BibliographicLevel::SERIAL_COMPONENT_PART,
                            GetPPN(ppn));
}


void GetCSVEntries(const std::string &csv_file, std::vector<std::vector<std::string>> * const lines) {
    TextUtil::ParseCSVFileOrDie(csv_file, lines);
    // Needed since ParseCSVFileOrDie() cannot cope with empty fields at the end
    auto has_more_columns = [](const std::vector<std::string> &a, const std::vector<std::string> &b) { return a.size() < b.size(); };
    auto max_columns_element(std::max_element(lines->begin(), lines->end(), has_more_columns));
    unsigned max_columns(max_columns_element->size());
    for (auto &line : *lines)
        line.resize(max_columns);
}


void InsertAuthors(MARC::Record * const record, const std::string &author1, const std::string &author_etal) {
    if (author1.length()) {
        MARC::Subfields author_subfields({ { 'a', author1 }, { '4', "aut" }, { 'e', "VerfasserIn" } });
        record->insertField("100", author_subfields, '1');
    } else
        LOG_WARNING("No author for " + record->getControlNumber());

    if (author_etal.length()) {
        std::vector<std::string> further_authors;
        StringUtil::SplitThenTrim(author_etal, ";", "\n ", &further_authors);
        for (const std::string &further_author : further_authors) {
            if (not further_author.length())
                continue;
            MARC::Subfields further_author_subfields({ { 'a', further_author }, { '4', "aut" }, { 'e', "VerfasserIn" } });
            record->insertField("700", further_author_subfields, '1');
        }
    }
}


void InsertTitle(MARC::Record * const record, const std::string &data) {
    if (data.length())
        record->insertField("245", { { 'a', data } }, '1', '0');
    else
        LOG_WARNING("No title for " + record->getControlNumber());
}


void InsertCreationDates(MARC::Record * const record, const std::string &year) {
    if (not year.empty())
        record->insertField("264", { { 'c', year } }, ' ', '1');
}


void InsertDOI(MARC::Record * const record, const std::string &doi) {
    if (doi.empty())
        return;
    record->insertField("024", { { 'a', doi }, { '2', "doi" } }, '7');
    record->insertField("856", { { 'u', "https://doi.org/" + doi }, { 'z', "ZZ" } }, '4', '0');
}


void InsertURL(MARC::Record * const record, const std::string &data) {
    if (data.length())
        record->insertField("856", { { 'u', data }, { 'z', "ZZ" } }, '4', '0');
    else
        LOG_WARNING("No URL for " + record->getControlNumber());
}


void InsertReferenceHint(MARC::Record * const record, const std::string &data) {
    if (data.length())
        record->insertField("500", { { 'a', "Verweis auf \"" + data + "\"" } });
}


void InsertLanguage(MARC::Record * const record, const std::string &data) {
    if (not TranslationUtil::IsValidInternational2LetterCode(data))
        LOG_ERROR("Invalid language code \"" + data + "\"");
    const std::string german_language_code(TranslationUtil::MapInternational2LetterCodeToGerman3Or4LetterCode(data));
    const std::string language_code(TranslationUtil::MapGermanLanguageCodesToFake3LetterEnglishLanguagesCodes(german_language_code));
    record->insertField("041", { { 'a', language_code } });
}

void InsertVolume(MARC::Record * const record, const std::string &data) {
    if (not data.empty())
        record->insertField("VOL", { { 'a', data } });
}


} // end unnamed namespace


int Main(int argc, char **argv) {
    if (argc != 3)
        Usage();

    std::vector<std::vector<std::string>> lines;
    GetCSVEntries(argv[1], &lines);
    std::unique_ptr<MARC::Writer> marc_writer(MARC::Writer::Factory(argv[2]));
    unsigned generated_records(0);

    for (auto &line : lines) {
        MARC::Record *new_record = CreateNewRecord(line[BOOKPARTID]);
        new_record->insertField("005", TimeUtil::GetCurrentDateAndTime("%Y%m%d%H%M%S") + ".0");
        new_record->insertField("007", "cr|||||");
        InsertAuthors(new_record, line[AUTHOR1], line[AUTHOR_ETAL]);
        InsertTitle(new_record, line[TITLE]);
        InsertDOI(new_record, line[DOI]);
        InsertLanguage(new_record, line[LANG]);
        InsertCreationDates(new_record, line[EPUB]);
        InsertURL(new_record, line[URL]);
        InsertReferenceHint(new_record, line[ZIELSTICHWORT]);
        new_record->insertField("TYP", { { 'a', PSEUDO_PPN_PREFIX } });
        InsertVolume(new_record, line[VOL]);
        marc_writer->write(*new_record);
        ++generated_records;
    }

    std::cerr << "Generated " << generated_records << " MARC records\n";

    return EXIT_SUCCESS;
}
