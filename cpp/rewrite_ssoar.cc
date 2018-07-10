/** \brief A tool for rewriting  information in ssoar data
 *  \author Johannes Riedl
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
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include "Compiler.h"
#include "FileUtil.h"
#include "MARC.h"
#include "MiscUtil.h"
#include "RegexMatcher.h"
#include "StringUtil.h"
#include "TextUtil.h"
#include "util.h"


namespace {


[[noreturn]] void Usage() {
    std::cerr << "Usage: " << ::progname << " [--input-format=(marc-21|marc-xml)] marc_input marc_output\n";
    std::exit(EXIT_FAILURE);
}


void Assemble773Article(MARC::Subfields * const _773subfields, const std::string &title = "",
                        const std::string &year = "", const std::string &pages = "",
                        const std::string &volinfo = "", const std::string &edition = "")
{
    if (not (title.empty() and volinfo.empty() and pages.empty() and year.empty() and edition.empty()))
       _773subfields->addSubfield('i', "In:");
    if (not title.empty())
        _773subfields->addSubfield('a', StringUtil::Trim(title));
    if (not volinfo.empty())
        _773subfields->addSubfield('g', "volume: " + volinfo);
    if (not pages.empty())
        _773subfields->addSubfield('g', "pages: " + pages);
    if (not year.empty())
        _773subfields->addSubfield('g', "year: " + year);
    if (not edition.empty())
        _773subfields->addSubfield('g', "edition: "  + edition);
}


void Assemble773Book(MARC::Subfields * const _773subfields, const std::string &title = "",
                     const std::string &authors = "", const std::string &year = "",
                     const std::string &pages = "", const std::string &isbn = "")
{
    if (not (title.empty() and authors.empty() and year.empty() and pages.empty() and isbn.empty()))
       _773subfields->addSubfield('i', "In:");
    if (not title.empty()) {
        if (not authors.empty())
            _773subfields->addSubfield('t', StringUtil::Trim(title));
        else
            _773subfields->addSubfield('a', StringUtil::Trim(title));
    }
    if (not authors.empty())
        _773subfields->addSubfield('a', authors);
    if (not year.empty())
        _773subfields->addSubfield('d', year);
    if ( not pages.empty())
        _773subfields->addSubfield('g', "pages:" + pages);
    if (not isbn.empty())
        _773subfields->addSubfield('o', isbn);
}


void ParseSuperior(const std::string &_500a_content, MARC::Subfields * const _773subfields) {
   // Belegung nach BSZ-Konkordanz
   // 773 $a "Geistiger Schöpfer"
   // 773 08 $i "Beziehungskennzeichnung" (== Übergerordnetes Werk)
   // 773 $d Jahr
   // 773 $t Titel (wenn Autor nicht vorhanden, dann stattdessen $a)
   // 773 $g Bandzählung [und weitere Angaben]
   // 773 $o "Sonstige Identifier für die andere Ausgabe" (ISBN)

   // 500 Structure for books
   // Must be checked first since it is more explicit
   // Normally it is Author(s) : Title. Year. S. xxx. ISBN
   static const std::string book_regex_1("^([^:]*):\\s*(.+)?\\s*(\\d{4})\\.(?=\\s*S\\.\\s*([\\d\\-]+)\\.\\s*ISBN\\s*([\\d\\-X]+))");
   static RegexMatcher * const book_matcher_1(RegexMatcher::RegexMatcherFactoryOrDie(book_regex_1));
   // Authors : Title. Year. Pages
   static const std::string book_regex_2("^([^:]*):\\s*(.+)?\\s*(\\d{4})\\.(?=\\sS\\.\\s([\\d\\-]+))");
   static RegexMatcher * const book_matcher_2(RegexMatcher::RegexMatcherFactoryOrDie(book_regex_1));
   // Authors : Title. Year. ISBN
   static const std::string book_regex_3("^([^:]*):\\s*(.+)?\\s*(\\d{4})\\.(?=\\s*ISBN\\s*([\\d\\-X]+))");
   static RegexMatcher * const book_matcher_3(RegexMatcher::RegexMatcherFactoryOrDie(book_regex_2));

   // 500 Structure fields for articles
   // Normally Journal ; Edition String ; Page (??)
   static const std::string article_regex_1("^([^;]*)\\s*;\\s*([^;]*)\\s*;\\s*([\\d\\-]*)\\s*");
   static RegexMatcher * const article_matcher_1(RegexMatcher::RegexMatcherFactoryOrDie(article_regex_1));
   // Journal; Pages
   static const std::string article_regex_2("^([^;]*)\\s*;\\s*([\\d\\-]*)\\s*");
   static RegexMatcher * const article_matcher_2(RegexMatcher::RegexMatcherFactoryOrDie(article_regex_2));
   // Journal (Year)
   static const std::string article_regex_3("^(.*)\\s*\\((\\d{4})\\)");
   static RegexMatcher * const article_matcher_3(RegexMatcher::RegexMatcherFactoryOrDie(article_regex_3));

   if (book_matcher_1->matched(_500a_content)) {
       const std::string authors((*book_matcher_1)[1]);
       const std::string title((*book_matcher_1)[2]);
       const std::string year((*book_matcher_1)[3]);
       const std::string pages((*book_matcher_1)[4]);
       const std::string isbn((*book_matcher_1)[5]);
       Assemble773Book(_773subfields, title, authors, year, pages, isbn);
   } else if (book_matcher_2->matched(_500a_content)) {
       const std::string authors((*book_matcher_2)[1]);
       const std::string title((*book_matcher_2)[2]);
       const std::string year((*book_matcher_2)[3]);
       Assemble773Book(_773subfields, title, authors, year);
   } else if (book_matcher_3->matched(_500a_content)) {
       const std::string authors((*book_matcher_3)[1]);
       const std::string title((*book_matcher_3)[2]);
       const std::string year((*book_matcher_3)[3]);
       const std::string isbn((*book_matcher_3)[4]);
       Assemble773Book(_773subfields, title, authors, year, "", isbn);
   } else if (article_matcher_1->matched(_500a_content)) {
       const std::string title((*article_matcher_1)[1]);
       const std::string volinfo((*article_matcher_1)[2]);
       const std::string page((*article_matcher_1)[3]);
       Assemble773Article(_773subfields, title, "", page, volinfo, "");
   } else if (article_matcher_2->matched(_500a_content)) {
       // See whether we can extract further information
       const std::string title_and_spec((*article_matcher_2)[1]);
       const std::string pages((*article_matcher_2)[2]);
       static const std::string title_and_spec_regex("^([^(]*)\\s*\\((\\d{4})\\)\\s*(\\d+)\\s*");
       static RegexMatcher * const title_and_spec_matcher(RegexMatcher::RegexMatcherFactoryOrDie(title_and_spec_regex));
       if (title_and_spec_matcher->matched(title_and_spec)) {
          const std::string title((*title_and_spec_matcher)[1]);
          const std::string year((*title_and_spec_matcher)[2]);
          const std::string edition((*title_and_spec_matcher)[3]);
          Assemble773Article(_773subfields, title, year, pages, "", edition);
       } else
          Assemble773Article(_773subfields, title_and_spec, "", pages);
   } else if (article_matcher_3->matched(_500a_content)) {
       const std::string title((*article_matcher_3)[1]);
       const std::string year((*article_matcher_3)[2]);
       Assemble773Article(_773subfields, title, year);
   } else
       LOG_WARNING("No matching regex for " + _500a_content);
}


void InsertSigilTo003(MARC::Record * const record, bool * const modified_record) {
    record->insertField("003", "INSERT_VALID_SIGEL_HERE");
    *modified_record = true;
}


// Rewrite to 041$h or get date from 008
void InsertLanguageInto041(MARC::Record * const record, bool * const modified_record) {
     for (auto &field : record->getTagRange("041")) {
         if (field.hasSubfield('h'))
             return;

         // Check whether the information is already in the $a field
         static const std::string valid_language_regex("([a-zA-Z]{3})$");
         static RegexMatcher * const valid_language_matcher(RegexMatcher::RegexMatcherFactoryOrDie(valid_language_regex));
         std::string language;
         if (valid_language_matcher->matched(field.getFirstSubfieldWithCode('a'))) {
             field.replaceSubfieldCode('a', 'h');
             *modified_record = true;
             return;
         } else {
             const std::string _008_field(record->getFirstFieldContents("008"));
             if (not valid_language_matcher->matched(_008_field)) {
                 LOG_WARNING("Invalid language code " + language);
                 continue;
             }
             record->addSubfield("041", 'h', language);
             *modified_record = true;
             return;
        }
    }
}


void InsertYearTo264c(MARC::Record * const record, bool * const modified_record) {
    for (const auto &field : record->getTagRange("264")) {
        if (field.hasSubfield('c'))
            return;
        // Extract year from 008 if available
        const std::string _008_field(record->getFirstFieldContents("008"));
        const std::string year(_008_field.substr(7,4));
        record->addSubfield("264", 'c', year);
        *modified_record = true;
        return;
    }
}


void RewriteSuperiorReference(MARC::Record * const record, bool * const modified_record) {
    if (record->findTag("773") != record->end())
        return;

    // Check if we have matching 500 field
    const std::string superior_string("^In:[\\s]*(.*)");
    RegexMatcher * const superior_matcher(RegexMatcher::RegexMatcherFactory(superior_string));

    for (auto &field : record->getTagRange("500")) {
        const auto subfields(field.getSubfields());
        for (const auto &subfield : subfields) {
            if (subfield.code_ == 'a' and superior_matcher->matched(subfield.value_)) {
                MARC::Subfields new_773_Subfields;
                // Parse Field Contents
                ParseSuperior((*superior_matcher)[1], &new_773_Subfields);
                // Write 773 Field
                if (not new_773_Subfields.empty()) {
                    record->insertField("773", new_773_Subfields, '0', '8');
                    *modified_record = true;
                }
            }
        }
    }
}


void ProcessRecords(MARC::Reader * const marc_reader, MARC::Writer * const marc_writer) {
    unsigned record_count(0), modified_count(0);
    while (MARC::Record record = marc_reader->read()) {
        ++record_count;
        bool modified_record(false);
        InsertSigilTo003(&record, &modified_record);
        InsertLanguageInto041(&record, &modified_record);
        InsertYearTo264c(&record, &modified_record);
        RewriteSuperiorReference(&record, &modified_record);
        marc_writer->write(record);
        if (modified_record)
            ++modified_count;
    }

    LOG_INFO("Modified " + std::to_string(modified_count) + " of " + std::to_string(record_count) + " records");
}


} // unnamed namespace


int Main(int argc, char **argv) {
    ::progname = argv[0];
    MARC::FileType reader_type(MARC::FileType::AUTO);
    if (argc == 4) {
        if (std::strcmp(argv[1], "--input-format=marc-21") == 0)
            reader_type = MARC::FileType::BINARY;
        else if (std::strcmp(argv[1], "--input-format=marc-xml") == 0)
            reader_type = MARC::FileType::XML;
        else
            Usage();
        ++argv, --argc;
    }

    if (argc != 3)
        Usage();

    const std::string marc_input_filename(argv[1]);
    const std::string marc_output_filename(argv[2]);
    if (unlikely(marc_input_filename == marc_output_filename))
        LOG_ERROR("Title data input file name equals output file name!");
    std::unique_ptr<MARC::Reader> marc_reader(MARC::Reader::Factory(marc_input_filename, reader_type));
    std::unique_ptr<MARC::Writer> marc_writer(MARC::Writer::Factory(marc_output_filename));
    ProcessRecords(marc_reader.get() , marc_writer.get());
    return EXIT_SUCCESS;
}
