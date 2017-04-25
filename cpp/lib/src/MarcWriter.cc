/** \brief Implementation of writer classes for MARC files.
 *  \author Oliver Obenland (oliver.obenland@uni-tuebingen.de)
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2017 Universitätsbibliothek Tübingen.  All rights reserved.
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

#include "MarcRecord.h"
#include "Compiler.h"
#include "FileUtil.h"
#include "MarcWriter.h"
#include "StringUtil.h"
#include "util.h"


static const size_t MAX_MARC_21_RECORD_LENGTH(99999);
static char write_buffer[MAX_MARC_21_RECORD_LENGTH]; // Possibly too big for the stack!


// Returns true if we can add the new field to our record w/o overflowing the maximum size of a binary
// MARC-21 record, o/w we return false.
static bool inline NewFieldDoesFit(const size_t base_address, const size_t current_record_length,
                                   const size_t next_field_length)
{
    return base_address + DirectoryEntry::DIRECTORY_ENTRY_LENGTH + current_record_length + next_field_length
           + 1 /* for the field terminator byte */ <= MAX_MARC_21_RECORD_LENGTH;
}


/**
 * We determine the record dimensions by adding sizes of fields one-by-one (starting with the field represented by
 * "directory_iter") while we do not overflow the maximum
 * size of a binary MARC-21 record.
 */
static void inline DetermineRecordDimensions(const size_t control_number_field_length,
                                             std::vector<DirectoryEntry>::const_iterator directory_iter,
                                             const std::vector<DirectoryEntry>::const_iterator &end_iter,
                                             size_t * const number_of_directory_entries, size_t * const base_address,
                                             size_t * const record_length)
{
    *number_of_directory_entries = 0;
    *base_address = DirectoryEntry::DIRECTORY_ENTRY_LENGTH /* for the control number field */
                    + Leader::LEADER_LENGTH + 1 /* for directory separator byte */;
    *record_length = control_number_field_length + 1 /* for end of record byte */;

    // Now we add fields one-by-one while taking care not to overflow the maximum record size:
    for (/* empty */;
         directory_iter < end_iter
         and NewFieldDoesFit(*base_address, *record_length, directory_iter->getFieldLength());
         ++directory_iter)
    {
        *base_address += DirectoryEntry::DIRECTORY_ENTRY_LENGTH;
        *record_length += directory_iter->getFieldLength();
        ++*number_of_directory_entries;
    }

    *record_length += *base_address;
}


static void inline WriteToBuffer(char *&dest, const std::string &data) {
    std::memcpy(dest, data.data(), data.size());
    dest += data.size();
}


static void inline WriteToBuffer(char *&dest, const char * const source, size_t offset, size_t length) {
    std::memcpy(dest, source + offset, length);
    dest += length;
}


static void inline WriteDirEntryToBuffer(char *&directory_pointer, const DirectoryEntry &dir_entry) {
    const MarcTag &tag(dir_entry.getTag());
    WriteToBuffer(directory_pointer, tag.c_str(), DirectoryEntry::TAG_LENGTH, 0);
    WriteToBuffer(directory_pointer, StringUtil::PadLeading(std::to_string(dir_entry.getFieldLength()), 4, '0'));
    WriteToBuffer(directory_pointer, StringUtil::PadLeading(std::to_string(dir_entry.getFieldOffset()), 5, '0'));
}


void BinaryMarcWriter::write(const MarcRecord &record) {
    const std::string control_number(record.getControlNumber());
    const size_t control_number_field_length(control_number.size() + 1);

    auto directory_iter(record.directory_entries_.cbegin());
    if (unlikely(directory_iter == record.directory_entries_.cend()))
        Error("BinaryMarcWriter::write: can't write a record w/ an empty directory!");
    if (unlikely(directory_iter->getTag() != "001"))
        Error("BinaryMarcWriter::write: first directory entry has to be 001! Found: "
              + directory_iter->getTag().to_string() + " (Control number: " + record.getControlNumber() + ")");
    ++directory_iter;

    while (directory_iter < record.directory_entries_.cend()) {
        size_t number_of_directory_entries, record_length, base_address_of_data;
        DetermineRecordDimensions(control_number_field_length, directory_iter, record.directory_entries_.cend(),
                                  &number_of_directory_entries, &base_address_of_data, &record_length);

        // Update and write the leader:
        char *leader_pointer(write_buffer);
        record.leader_.setBaseAddressOfData(base_address_of_data);
        record.leader_.setRecordLength(record_length);
        record.leader_.setMultiPartRecord(directory_iter + number_of_directory_entries + 1
                                          < record.directory_entries_.cend());
        WriteToBuffer(leader_pointer, record.leader_.toString());

        // Write a control number directory entry for each record as the first entry in the directory section:
        char *directory_pointer(write_buffer + Leader::LEADER_LENGTH);
        WriteDirEntryToBuffer(directory_pointer, record.directory_entries_.front());

        size_t field_data_offset(0);
        size_t field_data_length(control_number_field_length);

        const std::vector<DirectoryEntry>::const_iterator end_iter(directory_iter + number_of_directory_entries);
        char *field_data_pointer(write_buffer + base_address_of_data);
        for (; directory_iter < end_iter; ++directory_iter) {
            WriteDirEntryToBuffer(directory_pointer, *directory_iter);
            WriteToBuffer(field_data_pointer, record.field_data_.data(), field_data_offset, field_data_length);
            field_data_offset = directory_iter->getFieldOffset();
            field_data_length = directory_iter->getFieldLength();
        }
        WriteToBuffer(directory_pointer, "\x1E");
        WriteToBuffer(field_data_pointer, "\x1D");
        output_->write(write_buffer, record_length);
    }
}


XmlMarcWriter::XmlMarcWriter(File * const output_file, const unsigned indent_amount,
                             const XmlWriter::TextConversionType text_conversion_type)
{
    xml_writer_ = new MarcXmlWriter(output_file, indent_amount, text_conversion_type);
}


void XmlMarcWriter::write(const MarcRecord &record) {
    xml_writer_->openTag("marc:record");

    record.leader_.setRecordLength(0);
    record.leader_.setBaseAddressOfData(0);
    xml_writer_->writeTagsWithData("marc:leader", record.leader_.toString(), /* suppress_newline = */ true);

    for (unsigned entry_no(0); entry_no < record.directory_entries_.size(); ++entry_no) {
        const DirectoryEntry &dir_entry(record.directory_entries_[entry_no]);
        if (dir_entry.isControlFieldEntry())
            xml_writer_->writeTagsWithData("marc:controlfield",
                                           { std::make_pair("tag", dir_entry.getTag().to_string()) },
                                           record.getFieldData(entry_no),
                    /* suppress_newline = */ true);
        else { // We have a data field.
            const std::string data(record.getFieldData(entry_no));
            xml_writer_->openTag("marc:datafield",
                                { std::make_pair("tag", dir_entry.getTag().to_string()),
                                  std::make_pair("ind1", std::string(1, data[0])),
                                  std::make_pair("ind2", std::string(1, data[1]))
                                });

            std::string::const_iterator ch(data.cbegin() + 2 /* Skip over the indicators. */);

            while (ch != data.cend()) {
                if (*ch != '\x1F')
                    std::runtime_error("in XmlMarcWriter::write: expected subfield code delimiter not found! Found "
                                       + std::string(1, *ch) + "! (Control number is " + record.getControlNumber()
                                       + ".)");

                ++ch;
                if (ch == data.cend())
                    std::runtime_error("in XmlMarcWriter::write: unexpected subfield data end while expecting a "
                                       "subfield code!");
                const std::string subfield_code(1, *ch++);

                std::string subfield_data;
                while (ch != data.cend() and *ch != '\x1F')
                    subfield_data += *ch++;
                if (subfield_data.empty())
                    continue;

                xml_writer_->writeTagsWithData("marc:subfield", { std::make_pair("code", subfield_code) },
                                              subfield_data, /* suppress_newline = */ true);
            }

            xml_writer_->closeTag(); // Close "marc:datafield".
        }
    }

    xml_writer_->closeTag(); // Close "marc:record".
}


std::unique_ptr<MarcWriter> MarcWriter::Factory(const std::string &output_filename, WriterType writer_type,
                                                const WriterMode writer_mode)
{
    std::unique_ptr<File> output(writer_mode == WriterMode::OVERWRITE ? FileUtil::OpenOutputFileOrDie(output_filename)
                                                                      : FileUtil::OpenForAppeningOrDie(output_filename));
    if (writer_type == AUTO) {
        if (StringUtil::EndsWith(output_filename, ".mrc") or StringUtil::EndsWith(output_filename, ".marc"))
            writer_type = BINARY;
        else if (StringUtil::EndsWith(output_filename, ".xml"))
            writer_type = XML;
        else
            throw std::runtime_error("in MarcWriter::Factory: WriterType is AUTO but filename \""
                                     + output_filename + "\" does not end in \".mrc\" or \".xml\"!");
    }
    return (writer_type == XML) ? std::unique_ptr<MarcWriter>(new XmlMarcWriter(output.release()))
                                : std::unique_ptr<MarcWriter>(new BinaryMarcWriter(output.release()));
}
