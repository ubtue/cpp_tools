/** \file   PdfUtil.cc
 *  \brief  Implementation of functions relating to PDF documents.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2015,2017 Universitätsbibliothek Tübingen.  All rights reserved.
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
#include "PdfUtil.h"
#include <leptonica/allheaders.h>
#include <tesseract/baseapi.h>
#include "ExecUtil.h"
#include "FileUtil.h"
#include "MediaTypeUtil.h"
#include "StringUtil.h"
#include "util.h"

namespace PdfUtil {


bool ExtractText(const std::string &pdf_document, std::string * const extracted_text,
                 const std::string &start_page, const std::string &end_page)
{
    static std::string pdftotext_path;
    if (pdftotext_path.empty())
        pdftotext_path = ExecUtil::LocateOrDie("pdftotext");

    const FileUtil::AutoTempFile auto_temp_file1;
    const std::string &input_filename(auto_temp_file1.getFilePath());
    if (not FileUtil::WriteString(input_filename, pdf_document)) {
        LOG_WARNING("can't write document to \"" + input_filename + "\"!");
        return false;
    }

    const FileUtil::AutoTempFile auto_temp_file2;
    const std::string &output_filename(auto_temp_file2.getFilePath());
    std::vector<std::string> pdftotext_params = { "-enc", "UTF-8", "-nopgbrk" };
    if (not start_page.empty())
        pdftotext_params.insert(pdftotext_params.end(), { "-f", start_page });
    if (not end_page.empty())
        pdftotext_params.insert(pdftotext_params.end(), { "-l", end_page });
    pdftotext_params.insert(pdftotext_params.end(), { input_filename, output_filename });
    const int retval(ExecUtil::Exec(pdftotext_path, pdftotext_params));
    if (retval != 0) {
        LOG_WARNING("failed to execute \"" + pdftotext_path + "\"!");
        return false;
    }

    if (not FileUtil::ReadString(output_filename, extracted_text)) {
        LOG_WARNING("failed to read extracted text from \"" + output_filename + "\"!");
        return false;
    }

    return not extracted_text->empty();
}


bool PdfFileContainsNoText(const std::string &path) {
    static std::string pdffonts_path;
    if (pdffonts_path.empty())
        pdffonts_path = ExecUtil::LocateOrDie("pdffonts");

    const FileUtil::AutoTempFile auto_temp_file;
    const std::string &output_filename(auto_temp_file.getFilePath());
    const int retval(ExecUtil::Exec(pdffonts_path, { path }, "", output_filename));
    if (retval == 0) {
        std::string output;
        if (not FileUtil::ReadString(output_filename, &output))
            return false;
        return output.length() == 188; // Header only?
    }

    return retval == 0;
}


bool PdfDocContainsNoText(const std::string &document) {
    const FileUtil::AutoTempFile auto_temp_file;
    const std::string &output_filename(auto_temp_file.getFilePath());
    if (not FileUtil::WriteString(output_filename, document))
        return false;
    return PdfFileContainsNoText(output_filename);
}


bool GetTextFromImage(const std::string &img_path, const std::string &tesseract_language_code,
                      std::string * const extracted_text)
{
    tesseract::TessBaseAPI * const api(new tesseract::TessBaseAPI());
    if (api->Init(nullptr, tesseract_language_code.c_str())) {
        LOG_WARNING("Could not initialize Tesseract API!");
        return false;
    }

    const std::string filetype(MediaTypeUtil::GetFileMediaType(img_path));

    // Special Handling for tiff multipages
    if (filetype == "image/tiff") {
        extracted_text->clear();
        Pixa *multipage_image(pixaReadMultipageTiff(img_path.c_str()));
        for (l_int32 offset(0); offset < multipage_image->n; ++offset) {
             LOG_INFO("Extracting page " + std::to_string(offset + 1));
             api->SetImage(multipage_image->pix[offset]);
             char *utf8_page(api->GetUTF8Text());
             extracted_text->append(utf8_page);
             delete[] utf8_page;
        }
        api->End();
        delete api;
        pixaDestroy(&multipage_image);
        delete multipage_image;

    } else {
        Pix *image(pixRead(img_path.c_str()));
        api->SetImage(image);
        char *utf8_text(api->GetUTF8Text());
        *extracted_text = utf8_text;
        delete[] utf8_text;
        api->End();
        delete api;
        pixDestroy(&image);
        delete image;

    }
    return not extracted_text->empty();
}


bool GetTextFromImagePDF(const std::string &pdf_document, const std::string &tesseract_language_code,
                         std::string * const extracted_text, unsigned timeout)
{
    extracted_text->clear();

    static std::string pdf_images_script_path(ExecUtil::LocateOrDie("pdfimages"));

    const FileUtil::AutoTempDirectory auto_temp_dir;
    const std::string &output_dirname(auto_temp_dir.getDirectoryPath());
    const std::string input_filename(output_dirname + "/in.pdf");
    if (not FileUtil::WriteString(input_filename, pdf_document)) {
        LOG_WARNING("failed to write the PDF to a temp file!");
        return false;
    }

    if (ExecUtil::Exec(pdf_images_script_path, { input_filename, output_dirname + "/out" }, "", "", "", timeout) != 0) {
        LOG_WARNING("failed to extract images from PDF file!");
        return false;
    }

    std::vector<std::string> pdf_image_filenames;
    if (FileUtil::GetFileNameList("out.*", &pdf_image_filenames, output_dirname) == 0) {
        LOG_WARNING("PDF did not contain any images!");
        return false;
    }

    for (const std::string &pdf_image_filename : pdf_image_filenames) {
        std::string image_text;
        if (not GetTextFromImage(output_dirname + "/" + pdf_image_filename, tesseract_language_code, &image_text)) {
            LOG_WARNING("failed to extract text from image " + pdf_image_filename);
            return false;
        }
         *extracted_text += " " + image_text;
    }

    *extracted_text = StringUtil::TrimWhite(*extracted_text);
    return not extracted_text->empty();
}


bool GetOCRedTextFromPDF(const std::string &pdf_document_path, const std::string &tesseract_language_code,
                         std::string * const extracted_text, unsigned timeout) {
    extracted_text->clear();
    static std::string pdf_to_image_command(ExecUtil::LocateOrDie("convert"));
    const FileUtil::AutoTempDirectory auto_temp_dir;
    const std::string &image_dirname(auto_temp_dir.getDirectoryPath());
    const std::string temp_image_location = image_dirname + "/img.tiff";
    if (ExecUtil::Exec(pdf_to_image_command, { "-density", "300", pdf_document_path, "-depth", "8", "-strip",
                                               "-background", "white", "-alpha", "off", temp_image_location
                                             }, "", "", "", timeout) != 0) {
        LOG_WARNING("failed to convert PDF to image!");
        return false;
    }
    if (not GetTextFromImage(temp_image_location, tesseract_language_code, extracted_text))
        LOG_WARNING("failed to extract OCRed text");

    *extracted_text = StringUtil::TrimWhite(*extracted_text);
    return not extracted_text->empty();
}


bool ExtractPDFInfo(const std::string &pdf_document, std::string * const pdf_output) {
    static std::string pdfinfo_path;
    if (pdfinfo_path.empty())
        pdfinfo_path = ExecUtil::LocateOrDie("pdfinfo");
    const FileUtil::AutoTempFile auto_temp_file1;
    const std::string &input_filename(auto_temp_file1.getFilePath());
    if (not FileUtil::WriteString(input_filename, pdf_document)) {
        LOG_WARNING("can't write document to \"" + input_filename + "\"!");
        return false;
    }
    const FileUtil::AutoTempFile auto_temp_file2;
    const std::string &pdfinfo_output_filename(auto_temp_file2.getFilePath());

    std::vector<std::string> pdfinfo_params = { input_filename };
    const int retval(ExecUtil::Exec(pdfinfo_path, pdfinfo_params, pdfinfo_output_filename /* stdout */,
                     pdfinfo_output_filename /* stderr */));
    if (retval != 0) {
        LOG_WARNING("failed to execute \"" + pdfinfo_path + "\"!");
        return false;
    }
    std::string pdfinfo_output;
    if (unlikely(not FileUtil::ReadString(pdfinfo_output_filename, pdf_output)))
        LOG_ERROR("Unable to extract pdfinfo output");

    return true;
}


} // namespace PdfUtil
