/** \brief Convert Afo Register Entries to authority data
 *  \author Johannes Riedl
 *
 *  \copyright 2022 Universitätsbibliothek Tübingen.  All rights reserved.
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

#include <iomanip>
#include <iostream>
#include <string>
#include <unordered_set>
#include "MARC.h"
#include "FileUtil.h"
#include "StringUtil.h"
#include "TextUtil.h"
#include "util.h"

namespace {

const unsigned ROWS_IN_CSV(5);


[[noreturn]] void Usage() {
    ::Usage("afo_register_csv_file1 [... afo_register_csv_fileN ] marc_output");
}


struct AfOEntry {
    unsigned entry_num_;
    std::string keyword_;
    std::string internal_reference_keyword_;
    std::string literature_reference_;
    std::string comment_;

    AfOEntry(const unsigned &entry_num, const std::string &keyword,
             const std::string &internal_reference_keyword,
             const std::string &literature_reference, const std::string &comment) :
             entry_num_(entry_num), keyword_(keyword),
             internal_reference_keyword_(internal_reference_keyword),
             literature_reference_(literature_reference),
             comment_(comment) {}
    AfOEntry(const std::string keyword) : AfOEntry(0, keyword, "", "", "") {}
    bool operator==(const AfOEntry &rhs) const { return keyword_ == rhs.keyword_; }
    std::string toString() const { return std::to_string(entry_num_) + " AAA " + keyword_  + " BBB " + internal_reference_keyword_
                                    + " CCC " + literature_reference_ +  " DDD "  + comment_;
    }
    __attribute__((unused))
    friend std::ostream &operator<<(std::ostream &output, const AfOEntry &entry);
};


std::ostream &operator<<(std::ostream &output, const AfOEntry &entry) {
    output << entry.toString();
    return output;
}

} // unamed namespace

namespace std {

template <> struct hash<AfOEntry> {
    inline size_t operator()(const AfOEntry &afo_entry) const {
        return hash<std::string>()(afo_entry.keyword_);
    }
};

} // namespace std

namespace {


using AfOMultiSet = std::unordered_multiset<AfOEntry>;
using AfOMultiSetIterator = std::unordered_multiset<AfOEntry>::const_iterator;
using AfOMultiSetRange = std::pair<AfOMultiSetIterator, AfOMultiSetIterator>;


void AddToAfOMultiset(const std::string &afo_file_path, AfOMultiSet * const afo_multi_set) {
    std::vector<std::vector<std::string>> lines;
    TextUtil::ParseCSVFileOrDie(afo_file_path, &lines, '\t', '\0');
    unsigned linenum(0);
    for (auto &line : lines) {
       ++linenum;
       if (not StringUtil::IsUnsignedNumber(line[0])) {
           LOG_WARNING("Invalid content in line " + std::to_string(linenum) + "(" + StringUtil::Join(line, '\t') + ")");
           continue;
       }

       // Add missing columns
       for (auto i = line.size(); i < ROWS_IN_CSV; ++i)
           line.push_back("");
       AfOEntry afo_entry(std::stoi(line[0]), line[1], line[2], line[3], line[4]);
       afo_multi_set->emplace(afo_entry);
    }
}


void CleanCSVAndWriteToTempFile(const std::string &afo_file_path, FileUtil::AutoTempFile * const tmp_file) {
    std::unique_ptr<File> afo_tmp_file(FileUtil::OpenOutputFileOrDie(tmp_file->getFilePath()));
    for (auto line : FileUtil::ReadLines(afo_file_path)) {
        if (line.empty() or StringUtil::IsWhitespace(line))
            continue;
        StringUtil::RemoveTrailingLineEnd(&line);
        line = StringUtil::RightTrim(line, '\t');
        (*(afo_tmp_file.get())) << line << '\n';
    }
}

MARC::Record * CreateNewRecord(const std::string &ppn, const AfOMultiSetRange &range) {
    if (range.first == std::end(AfOMultiSet()))
        return nullptr;

    auto new_record(new MARC::Record("02676cz  a2200529n  4500"));
    new_record->insertControlField("001", ppn);
    if (unlikely(range.first->keyword_.empty())) {
        std::cerr << "KEYWORD EMPTY\n";
        new_record->insertField("150", { { 'a',  "EMPTY KEYWORD" } });
    } else
        new_record->insertField("150", { { 'a',  range.first->keyword_ } });
    for (auto entry = range.first; entry != range.second; ++entry) {
        if (not entry->literature_reference_.empty())
            new_record->insertField("500", { { 'a', entry->literature_reference_ } });
        if (not entry->comment_.empty())
            new_record->insertField("510", { { 'a', entry->comment_ } } );
        if (not entry->internal_reference_keyword_.empty())
            new_record->insertField("530", { { 'a', entry->internal_reference_keyword_ } });
    }
    return new_record;
}


std::string AssemblePPN(unsigned id) {
    std::ostringstream formatted_number;
    formatted_number << std::setfill('0') << std::setw(8) << id;
    return "KEA" + formatted_number.str();
}


} // unnamed namespace



int Main(int argc, char *argv[]) {
    if (argc < 3)
        Usage();

    const std::string marc_output_path(argv[argc - 1]);
    std::vector<std::string> afo_file_paths;
    for (int arg_index = 1; arg_index < argc - 1; ++arg_index)
         afo_file_paths.emplace_back(argv[arg_index]);

    AfOMultiSet afo_multi_set;
    for (const auto afo_file_path : afo_file_paths) {
        FileUtil::AutoTempFile tmp_file;
        CleanCSVAndWriteToTempFile(afo_file_path, &tmp_file);
        AddToAfOMultiset(tmp_file.getFilePath(), &afo_multi_set);
    }

    const std::unique_ptr<MARC::Writer> marc_writer(MARC::Writer::Factory(marc_output_path));
    unsigned id(0);
    for (auto entry_iterator = afo_multi_set.begin(); entry_iterator != afo_multi_set.end(); /* intentionally empty */ ) {
        if (auto same_keyword_range = afo_multi_set.equal_range(*entry_iterator); same_keyword_range.first != same_keyword_range.second) {
            auto new_record(CreateNewRecord(AssemblePPN(++id), same_keyword_range));
            if (new_record) {
               marc_writer->write(*new_record);
               delete new_record;
            }
            entry_iterator = same_keyword_range.second;
        } else
          ++entry_iterator;
    }
    return EXIT_SUCCESS;
}

