/** Test harness for MiscUtil::ExpandTemplate().
 */
#include <iostream>
#include <map>
#include <stdexcept>
#include <sstream>
#include <string>
#include <vector>
#include <cstdlib>
#include "FileUtil.h"
#include "StringUtil.h"
#include "Template.h"
#include "util.h"


void Usage() {
    std::cerr << "usage: " << ::progname
              << " template_filename var1_and_values [var2_and_values ... varN_and_values]\n";
    std::cerr << "       Variable names and values have to be separated by colons.\n";
    std::exit(EXIT_FAILURE);
}


void ExtractNamesAndValues(const int argc, char *argv[], Template::Map * const names_to_values_map) {
    names_to_values_map->clear();

    for (int arg_no(2); arg_no < argc; ++arg_no) {
        std::string arg(argv[arg_no]);
        std::vector<std::string> values;
        StringUtil::Split(arg, ':', &values);
        const std::string name(values.front());
        if (values.empty())
            ERROR(name + " is missing at least one value!");
        values.erase(values.begin());
        if (values.size() == 1)
            names_to_values_map->insertScalar(name, values.front());
        else
            names_to_values_map->insertArray(name, values);
    }
}


int main(int argc, char *argv[]) {
    ::progname = argv[0];
    if (argc < 3)
        Usage();

    try {
        const std::string template_filename(argv[1]);
        std::string template_string;
        if (not FileUtil::ReadString(template_filename, &template_string))
            logger->error("failed to read the template from \"" + template_filename + "\" for reading!");
        Template::Map names_to_values_map;
        ExtractNamesAndValues(argc, argv, &names_to_values_map);
        std::istringstream input(template_string);
        Template::ExpandTemplate(input, std::cout, names_to_values_map);
    } catch (const std::exception &x) {
        ERROR("caught exception: " + std::string(x.what()));
    }
}
