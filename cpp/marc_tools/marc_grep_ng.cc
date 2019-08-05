/** \brief MARC grep the Next Generation.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2019 Universitätsbibliothek Tübingen.  All rights reserved.
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
#include <cstring>
#include <cstdlib>
#include "Compiler.h"
#include "MARC.h"
#include "RegexMatcher.h"
#include "StringUtil.h"
#include "util.h"


namespace {


[[noreturn]] void Usage() {
    ::Usage("--query=query --output=field_and_or_subfield_list [--output-format=output_format] marc_file1 [marc_file2 .. marc_fileN]\n"
            "Queries have the following syntax:\n"
            "expression → term {OR term}\n"
            "term       → factor {AND factor}\n"
            "factor     → field_or_subfield_reference (== | !=) string_constant_or_regex\n"
            "factor     → NOT factor\n"
            "factor     → '(' expression ')'\n"
            "\'field_and_or_subfield_list\" is a semicolon-separated list of field or subfield references.  The special \"list\" is\n"
            "the assterisk which implies that an entire record will be output."
            );
    std::exit(EXIT_FAILURE);
}


enum TokenType { AND, OR, NOT, STRING_CONST, FUNC_CALL, OPEN_PAREN, CLOSE_PAREN, REGEX, EQUALS, NOT_EQUALS,
                 COMMA, ERROR, END_OF_QUERY };


class Tokenizer {
    struct FunctionDesc {
        std::string name_;
        unsigned argument_count_;
    };

    std::string::const_iterator next_ch_;
    const std::string::const_iterator end_;
    bool pushed_back_;
    TokenType last_token_;
    std::string last_error_message_;
    std::string last_string_;
    std::string last_function_name_;
    const static std::vector<FunctionDesc> function_descriptions_;
public:
    explicit Tokenizer(const std:: string &query): next_ch_(query.cbegin()), end_(query.cend()), pushed_back_(false) { }
    TokenType getNextToken();
    void ungetLastToken();
    inline const std::string &getLastErrorMessage() const { return last_error_message_; }
    inline const std::string &getLastString() const { return last_string_; }
    inline const std::string &getLastFunctionName() const { return last_function_name_; }
    static std::string TokenTypeToString(const TokenType token);
private:
    TokenType parseStringConstantOrRegex();
    bool isKnownFunctionName(const std::string &name_candidate) const;
};


const std::vector<Tokenizer::FunctionDesc> Tokenizer::function_descriptions_{ { "HasField", 1 }, { "HasSubfield", 2} };


TokenType Tokenizer::getNextToken() {
    if (pushed_back_) {
        pushed_back_ = false;
        return last_token_;
    }

    // Skip over spaces:
    while (next_ch_ != end_ and *next_ch_ == ' ')
        ++next_ch_;

    if (next_ch_ == end_)
        return last_token_ = END_OF_QUERY;

    if (*next_ch_ == '"' or *next_ch_ == '/')
        return last_token_ = parseStringConstantOrRegex();

    if (*next_ch_ == ',') {
        ++next_ch_;
        return last_token_ = COMMA;
    }

    if (*next_ch_ == '(') {
        ++next_ch_;
        return last_token_ = OPEN_PAREN;
    }

    if (*next_ch_ == ')') {
        ++next_ch_;
        return last_token_ = CLOSE_PAREN;
    }

    if (*next_ch_ == '=') {
        ++next_ch_;
        if (next_ch_ == end_ or *next_ch_ != '=') {
            last_error_message_ = "unexpected single equal sign found!";
            return ERROR;
        }
        return last_token_ = EQUALS;
    }

    if (*next_ch_ == '!') {
        ++next_ch_;
        if (next_ch_ == end_ or *next_ch_ != '=') {
            last_error_message_ = "unexpected single exclamation point found!";
            return ERROR;
        }
        return last_token_ = NOT_EQUALS;
    }

    if (unlikely(not StringUtil::IsAsciiLetter(*next_ch_))) {
        last_error_message_ = "expected ASCII letter!";
        return ERROR;
    }

    std::string id;
    while (next_ch_ != end_ and StringUtil::IsAsciiLetter(*next_ch_))
        id += *next_ch_;

    if (id == "AND")
        return last_token_ = AND;
    if (id == "OR")
        return last_token_ = OR;
    if (id == "NOT")
        return last_token_ = NOT;

    if (isKnownFunctionName(id)) {
        last_function_name_ = id;
        return last_token_ = FUNC_CALL;
    }

    last_error_message_ = "unknown function name \"" + id + "\"!";

    return ERROR;
}


void Tokenizer::ungetLastToken() {
    if (unlikely(pushed_back_))
        LOG_ERROR("can't push back two tokens in a row!");
    pushed_back_ = true;
}


TokenType Tokenizer::parseStringConstantOrRegex() {
    const char terminator(*next_ch_++);

    last_string_.clear();
    bool escaped(false);
    for (/* Intentionally empty! */; next_ch_ != end_; ++next_ch_) {
        if (escaped) {
            escaped = false;
            last_string_ += *next_ch_;
        } else if (*next_ch_ == terminator) {
            ++next_ch_;
            return (terminator == '"') ? STRING_CONST : REGEX;
        } else if (*next_ch_ == '\\')
            escaped = true;
        else
            last_string_ += *next_ch_;
    }

    last_error_message_ = "unterminated string constant or regex!";
    return ERROR;
}


bool Tokenizer::isKnownFunctionName(const std::string &name_candidate) const {
    for (const auto &function_description : function_descriptions_) {
        if (function_description.name_ == name_candidate)
            return true;
    }

    return false;
}


std::string Tokenizer::TokenTypeToString(const TokenType token) {
    switch (token) {
    case AND:
        return "AND";
    case OR:
        return "OR";
    case NOT:
        return "NOT";
    case STRING_CONST:
        return "string constant";
    case FUNC_CALL:
        return "function call";
    case OPEN_PAREN:
        return "(";
    case CLOSE_PAREN:
        return ")";
    case REGEX:
        return "regular expression";
    case EQUALS:
        return "==";
    case NOT_EQUALS:
        return "!=";
    case COMMA:
        return ",";
    case ERROR:
        return "unexpected input";
    case END_OF_QUERY:
        return "end-of-query";
    }
}


class Query {
    enum NodeType { AND_NODE, OR_NODE, STRING_COMPARISON_NODE, REGEX_COMPARISON_NODE };
    class Node {
    protected:
        bool invert_;
    protected:
        Node(): invert_(false) {}
    public:
        virtual ~Node() = 0;
        virtual NodeType getNodeType() const = 0;
        virtual bool eval(const MARC::Record &record) const = 0;
        inline void toggleInvert() { invert_ = not invert_; }
    };

    class AndNode final : public Node {
        std::vector<Node *> children_;
    public:
        explicit AndNode(std::vector<Node *> &children) { children.swap(children_); }
        ~AndNode() {
            for (const auto child_node : children_)
                delete child_node;
        }
        virtual NodeType getNodeType() const override { return AND_NODE; }
        virtual bool eval(const MARC::Record &record) const override;
    };

    class OrNode final : public Node {
        std::vector<Node *> children_;
    public:
        explicit OrNode(std::vector<Node *> &children) { children.swap(children_); }
        ~OrNode() {
            for (const auto child_node : children_)
                delete child_node;
        }
        virtual NodeType getNodeType() const override { return OR_NODE; }
        virtual bool eval(const MARC::Record &record) const override;
    };

    class StringComparisonNode final : public Node {
        MARC::Tag field_tag_;
        char subfield_code_;
        std::string string_const_;
    public:
        StringComparisonNode(const std::string &field_or_subfield_reference, const std::string &string_const, const bool invert)
            : field_tag_(field_or_subfield_reference.substr(0, MARC::Record::TAG_LENGTH)),
              subfield_code_(field_or_subfield_reference.length() > MARC::Record::TAG_LENGTH
                             ? field_or_subfield_reference[MARC::Record::TAG_LENGTH] : '\0'),
              string_const_(string_const) { invert_ = invert; }
        ~StringComparisonNode() = default;
        virtual NodeType getNodeType() const override { return STRING_COMPARISON_NODE; }
        virtual bool eval(const MARC::Record &record) const override;
    };

    class RegexComparisonNode final : public Node {
        MARC::Tag field_tag_;
        char subfield_code_;
        RegexMatcher *regex_;
        bool invert_;
    public:
        RegexComparisonNode(const std::string &field_or_subfield_reference, RegexMatcher * const regex, const bool invert)
            : field_tag_(field_or_subfield_reference.substr(0, MARC::Record::TAG_LENGTH)),
              subfield_code_(field_or_subfield_reference.length() > MARC::Record::TAG_LENGTH
                             ? field_or_subfield_reference[MARC::Record::TAG_LENGTH] : '\0'),
              regex_(regex), invert_(invert) { }
        ~RegexComparisonNode() { delete regex_; }
        virtual NodeType getNodeType() const override { return STRING_COMPARISON_NODE; }
        virtual bool eval(const MARC::Record &record) const override;
    };

    Tokenizer tokenizer_;
    Node *root_;
public:
    explicit Query(const std:: string &query);
    ~Query() { delete root_; }

    bool matched(const MARC::Record &record) const;
private:
    Node *parseExpression();
    Node *parseTerm();
    Node *parseFactor();
    static void DeletePointerVector(std::vector<Node *> &nodes);
};


Query::Node::~Node() {
    /* Intentionally empty! */
}


bool Query::AndNode::eval(const MARC::Record &record) const {
    for (const auto child_node : children_) {
        if (not child_node->eval(record))
            return invert_ ? true : false;
    }

    return true;
}


bool Query::OrNode::eval(const MARC::Record &record) const {
    for (const auto child_node : children_) {
        if (child_node->eval(record))
            return invert_ ? false : true;
    }

    return false;
}


bool Query::StringComparisonNode::eval(const MARC::Record &record) const {
    for (const auto &field : record.getTagRange(field_tag_)) {
        if (subfield_code_ == '\0') {
            if (field .getContents() == string_const_) {
                if (not invert_)
                    return true;
            } else if (invert_)
                return true;
        } else {
            const MARC::Subfields subfields(field.getSubfields());
            for (const auto &value_and_code : subfields) {
                if (value_and_code.code_ == subfield_code_) {
                    if (value_and_code.value_ == string_const_) {
                        if (not invert_)
                            return true;
                    } else if (invert_)
                        return true;
                }
            }
        }
    }

    return false;
}


bool Query::RegexComparisonNode::eval(const MARC::Record &record) const {
    for (const auto &field : record.getTagRange(field_tag_)) {
        if (subfield_code_ == '\0') {
            if (regex_->matched(field .getContents())) {
                if (not invert_)
                    return true;
            } else if (invert_)
                return true;
        } else {
            const MARC::Subfields subfields(field.getSubfields());
            for (const auto &value_and_code : subfields) {
                if (value_and_code.code_ == subfield_code_) {
                    if (regex_->matched(value_and_code.value_)) {
                        if (not invert_)
                            return true;
                    } else if (invert_)
                        return true;
                }
            }
        }
    }

    return false;
}


Query::Query(const std:: string &query)
    : tokenizer_(query), root_(parseExpression())
{
}


bool Query::matched(const MARC::Record &record) const {
    return root_->eval(record);
}


Query::Node *Query::parseExpression() {
    std::vector<Node *> children;
    children.emplace_back(parseTerm());

    TokenType token(tokenizer_.getNextToken());
    while (token == OR) {
        children.emplace_back(parseTerm());
        token = tokenizer_.getNextToken();
    }
    if (token == ERROR) {
        DeletePointerVector(children);
        throw std::runtime_error("error in OR expression: " + tokenizer_.getLastErrorMessage());
    }

    tokenizer_.ungetLastToken();
    return new OrNode(children);
}


Query::Node *Query::parseTerm() {
    std::vector<Node *> children;
    children.emplace_back(parseFactor());

    TokenType token(tokenizer_.getNextToken());
    while (token == AND) {
        children.emplace_back(parseFactor());
        token = tokenizer_.getNextToken();
    }
    if (token == ERROR) {
        DeletePointerVector(children);
        throw std::runtime_error("error in AND expression: " + tokenizer_.getLastErrorMessage());
    }

    tokenizer_.ungetLastToken();
    return new AndNode(children);
}


/*
    factor → field_or_subfield_reference (== | !=) string_constant_or_regex
    factor → NOT factor
    factor → '(' expression ')
*/
Query::Node *Query::parseFactor() {
    TokenType token(tokenizer_.getNextToken());
    if (token == STRING_CONST) {
        const std::string field_or_subfield_reference(tokenizer_.getLastString());
        if (field_or_subfield_reference.length() != MARC::Record::TAG_LENGTH
            and tokenizer_.getLastString().length() != MARC::Record::TAG_LENGTH + 1)
            throw std::runtime_error("invalid field or subfield reference \"" + field_or_subfield_reference + "\"!");

        token = tokenizer_.getNextToken();
        if (token != EQUALS and token != NOT_EQUALS)
            throw std::runtime_error("expected == or != after field or subfield reference, found "
                                     + Tokenizer::TokenTypeToString(token) + " instead!");

        const TokenType equality_operator(token);
        token = tokenizer_.getNextToken();
        if (token != STRING_CONST and token != REGEX)
            throw std::runtime_error("expected a string constant or a regex after " + Tokenizer::TokenTypeToString(equality_operator)
                                     + ", found " + Tokenizer::TokenTypeToString(token) + " instead!");
        RegexMatcher *regex_matcher;
        if (token == REGEX)
            regex_matcher = RegexMatcher::RegexMatcherFactoryOrDie(tokenizer_.getLastString());

        if (token == REGEX)
            return new RegexComparisonNode(field_or_subfield_reference, regex_matcher, equality_operator == EQUALS);
        else
            return new StringComparisonNode(field_or_subfield_reference, tokenizer_.getLastString(), equality_operator == EQUALS);
    }

    if (token == NOT) {
        Node * const factor_node(parseFactor());
        factor_node->toggleInvert();
        return factor_node;
    }

    if (token != OPEN_PAREN)
        throw std::runtime_error("opening parenthesis, NOT or string constant expected found " + Tokenizer::TokenTypeToString(token)
                                 + "instead!");

    Node * const expression_node(parseExpression());

    token = tokenizer_.getNextToken();
    if (token != CLOSE_PAREN) {
        delete expression_node;
        throw std::runtime_error("closing parenthesis after expression expected, found " + Tokenizer::TokenTypeToString(token) + "instead!");
    }

    return expression_node;
}


void Query::DeletePointerVector(std::vector<Query::Node *> &nodes) {
    for (auto node_ptr : nodes)
        delete node_ptr;
}


inline void ExtractRefsToSingleField(std::vector<std::string>::const_iterator &range_start,
                                     std::vector<std::string>::const_iterator &range_end,
                                     const std::vector<std::string>::const_iterator &list_end)
{
    range_end = range_start;
    while (range_end + 1 != list_end and std::memcmp(range_start->c_str(), (range_end + 1)->c_str(), MARC::Record::TAG_LENGTH) == 0)
        ++range_end;
    ++range_end; // half-open iterator interval, i.e. we want to point 1 past the end of the range`
}


void GenerateOutput(const MARC::Record::Field &/*field*/, const std::vector<std::string> &/*field_and_subfield_output_list*/,
                    const std::vector<std::string>::const_iterator &/*range_start*/, const std::vector<std::string>::const_iterator &/*range_end*/)
{
}


void ProcessRecords(const Query &query, MARC::Reader * const marc_reader, const std::vector<std::string> &field_and_subfield_output_list) {
    unsigned record_count(0), matched_count(0);
    while (const MARC::Record record = marc_reader->read()) {
        ++record_count;

        if (not query.matched(record))
            continue;
        ++matched_count;

        auto range_start(field_and_subfield_output_list.cbegin());
        auto range_end(range_start);
        ExtractRefsToSingleField(range_start, range_end, field_and_subfield_output_list.cend());
        auto field(record.begin());
        while (field != record.end() and range_start != field_and_subfield_output_list.cend()) {
            if (field->getTag() == range_start->substr(0, MARC::Record::TAG_LENGTH)) {
                GenerateOutput(*field, field_and_subfield_output_list, range_start, range_end);
                ++field;
            } else if (field->getTag() > range_start->substr(0, MARC::Record::TAG_LENGTH)) {
                range_start = range_end;
                while (range_start != field_and_subfield_output_list.cend()
                       and field->getTag() > range_start->substr(0, MARC::Record::TAG_LENGTH))
                    ++range_start;
                if (range_start != field_and_subfield_output_list.cend())
                    ExtractRefsToSingleField(range_start, range_end, field_and_subfield_output_list.cend());
            } else
                ++field;
        }
    }

    std::cerr << "Matched " << matched_count << " of " << record_count << " records.\n";
}


bool ParseOutputList(const std::string &output_list_candidate, std::vector<std::string> * const field_and_subfield_output_list) {
    if (StringUtil::SplitThenTrimWhite(output_list_candidate, ';', field_and_subfield_output_list, /* suppress_empty_components = */true)
        == 0)
        return false;

    for (const auto &field_or_subfield_reference_candidate : *field_and_subfield_output_list) {
        if (field_or_subfield_reference_candidate.length() != MARC::Record::TAG_LENGTH and
            field_or_subfield_reference_candidate.length() != MARC::Record::TAG_LENGTH + 1)
            return false;
    }
    std::sort(field_and_subfield_output_list->begin(), field_and_subfield_output_list->end());

    return field_and_subfield_output_list->size() == 1 and field_and_subfield_output_list->front() == "*";
}


} // unnamed namespace


int Main(int argc, char *argv[]) {
    if (argc < 4)
        Usage();

    const std::string QUERY_PREFIX("--query=");
    if (not StringUtil::StartsWith(argv[1], QUERY_PREFIX))
        LOG_ERROR("missing " + QUERY_PREFIX + "...!");
    const std::string query_str(argv[1] + QUERY_PREFIX.length());
    Query query(query_str);

    const std::string OUTPUT_PREFIX("--output=");
    if (not StringUtil::StartsWith(argv[2], OUTPUT_PREFIX))
        LOG_ERROR("missing " + OUTPUT_PREFIX + "...!");
    std::vector<std::string> field_and_subfield_output_list;
    if (not ParseOutputList(argv[2] + OUTPUT_PREFIX.length(), &field_and_subfield_output_list))
        LOG_ERROR("bad output specification: \"" + std::string(argv[2] + OUTPUT_PREFIX.length()));

    for (int arg_no(1); arg_no < argc; ++arg_no) {
        auto marc_reader(MARC::Reader::Factory(argv[1]));
        ProcessRecords(query, marc_reader.get(), field_and_subfield_output_list);
    }

    return EXIT_SUCCESS;
}
