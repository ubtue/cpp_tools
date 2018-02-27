/** \file   JSON.cc
 *  \brief  Implementation of JSON-related functionality.
 *  \author Dr. Johannes Ruscheinski (johannes.ruscheinski@uni-tuebingen.de)
 *
 *  \copyright 2017,2018 Universitätsbibliothek Tübingen.  All rights reserved.
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as
 *  published by the Free Software Foundation, either version 3 of the
 *  License, or (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero %General Public License for more details.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
#include "JSON.h"
#include <stdexcept>
#include <string>
#include <cctype>
#include "Compiler.h"
#include "StringUtil.h"
#include "TextUtil.h"


namespace JSON {


TokenType Scanner::getToken() {
    if (pushed_back_) {
        pushed_back_ = false;
        return pushed_back_token_;
    }

    skipWhite();

    if (unlikely(ch_ == end_))
        return END_OF_INPUT;

    switch (*ch_) {
    case ',':
        ++ch_;
        return COMMA;
    case ':':
        ++ch_;
        return COLON;
    case '{':
        ++ch_;
        return OPEN_BRACE;
    case '}':
        ++ch_;
        return CLOSE_BRACE;
    case '[':
        ++ch_;
        return OPEN_BRACKET;
    case ']':
        ++ch_;
        return CLOSE_BRACKET;
    case '"':
        return parseStringConstant();
    case 't':
        return expectSequence("true", TRUE_CONST);
    case 'f':
        return expectSequence("false", FALSE_CONST);
    case 'n':
        return expectSequence("null", NULL_CONST);
    case '+':
    case '-':
    case '0':
    case '1':
    case '2':
    case '3':
    case '4':
    case '5':
    case '6':
    case '7':
    case '8':
    case '9':
        return parseNumber();
    default:
        const std::string bad_char(::isprint(*ch_) ? std::string(1, *ch_)
                                   : "\\x" + StringUtil::ToHexString(static_cast<unsigned char>(*ch_)));
        last_error_message_ = "unexpected character '" + bad_char + "'!";
        return ERROR;
    }
}


void Scanner::ungetToken(const TokenType token) {
    if (unlikely(pushed_back_))
        throw std::runtime_error("in JSON::Scanner::ungetToken: can't push back two tokens in a row!");
    pushed_back_token_ = token;
    pushed_back_ = true;
}


void Scanner::skipWhite() {
    while (ch_ != end_ and isspace(*ch_)) {
        if (*ch_ == '\n')
            ++line_no_;
        ++ch_;
    }
}


TokenType Scanner::expectSequence(const std::string &sequence, const TokenType success_token) {
    for (const char expected_ch : sequence) {
        if (unlikely(ch_ == end_)) {
            last_error_message_ = "expected \"" + sequence + "\" but reached end-of-input!";
            return ERROR;
        } else if (unlikely(*ch_ != expected_ch)) {
            last_error_message_ = "expected \"" + sequence + "\" but found something else!";
            return ERROR;
        }

        ++ch_;
    }

    return success_token;
}


TokenType Scanner::parseNumber() {
    std::string number_as_string;
    if (*ch_ == '+' or *ch_ == '-')
        number_as_string += *ch_++;

    for (; ch_ != end_ and StringUtil::IsDigit(*ch_); ++ch_)
        number_as_string += *ch_;
    if (unlikely(number_as_string.empty())) {
        last_error_message_ = "missing digit or digits after a sign!";
        return ERROR;
    }

    if (ch_ == end_ or (*ch_ != '.' and *ch_ != 'e' and *ch_ != 'E')) {
        int64_t value;
        if (unlikely(not StringUtil::ToInt64T(number_as_string, &value))) {
            last_error_message_ = "failed to convert \"" + number_as_string + "\" to a 64-bit integer!";
            return ERROR;
        }

        last_integer_constant_ = value;
        return INTEGER_CONST;
    }

    if (*ch_ == '.') {
        for (++ch_; ch_ != end_ and StringUtil::IsDigit(*ch_); ++ch_)
            number_as_string += *ch_;
    }

    if (ch_ == end_ or (*ch_ != 'e' and  *ch_ != 'E')) {
        double value;
        if (unlikely(not StringUtil::ToDouble(number_as_string, &value))) {
            last_error_message_ = "failed to convert \"" + number_as_string + "\" to a floating point value!";
            return ERROR;
        }

        last_double_constant_ = value;
        return DOUBLE_CONST;
    }

    ++ch_;
    if (*ch_ == '+' or *ch_ == '-')
        number_as_string += *ch_++;
    if (unlikely(not StringUtil::IsDigit(*ch_))) {
        last_error_message_ = "missing digits for the exponent!";
        return ERROR;
    }
    for (; ch_ != end_ and StringUtil::IsDigit(*ch_); ++ch_)
        number_as_string += *ch_;

    double value;
    if (unlikely(not StringUtil::ToDouble(number_as_string, &value))) {
        last_error_message_ = "failed to convert \"" + number_as_string + "\" to a floating point value!";
        return ERROR;
    }

    last_double_constant_ = value;
    return DOUBLE_CONST;
}


// Converts the nnnn part of \unnnn to UTF-8. */
bool Scanner::UTF16EscapeToUTF8(std::string * const utf8) {
    std::string hex_codes;
    for (unsigned i(0); i < 4; ++i) {
        if (unlikely(ch_ == end_)) {
            last_error_message_ = "unexpected end-of-input while looking for a \\unnnn escape!";
            return false;
        }
        hex_codes += *ch_++;
    }

    uint16_t u1;
    if (unlikely(not StringUtil::ToUnsignedShort(hex_codes, &u1, 16))) {
        last_error_message_ = "invalid hex sequence \\u" + hex_codes + "!";
        return false;
    }

    if (TextUtil::IsValidSingleUTF16Char(u1)) {
        *utf8 = TextUtil::UTF32ToUTF8(TextUtil::UTF16ToUTF32(u1));
        return true;
    }

    if (unlikely(not TextUtil::IsFirstHalfOfSurrogatePair(u1))) {
        last_error_message_ = "\\u" + hex_codes + " is neither a standalone UTF-8 character nor a valid first half "
                              "of a UTF-16 surrogate pair!";
        return false;
    }

    if (unlikely(ch_ == end_ or *ch_++ != '\\')) {
        last_error_message_ = "could not find expected '\\' as part of the 2nd half of a surrogate pair!";
        return false;
    }
    if (unlikely(ch_ == end_ or *ch_++ != 'u')) {
        last_error_message_ = "could not find expected 'u' as part of the 2nd half of a surrogate pair!";
        return false;
    }

    hex_codes.clear();
    for (unsigned i(0); i < 4; ++i) {
        if (unlikely(ch_ == end_)) {
            last_error_message_ = "unexpected end of input while attempting to read the 2nd half of a surrogate "
                                  "pair!";
            return false;
        }
        hex_codes += *ch_++;
    }

    uint16_t u2;
    if (unlikely(not StringUtil::ToUnsignedShort(hex_codes, &u2, 16))) {
        last_error_message_ = "invalid hex sequence \\u" + hex_codes + " for the 2nd half of a surrogate pair!";
        return false;
    }
    if (unlikely(not TextUtil::IsSecondHalfOfSurrogatePair(u2))) {
        last_error_message_ = "invalid 2nd half of a surrogate pair: \\u" + hex_codes + "!";
        return false;
    }

    *utf8 = TextUtil::UTF32ToUTF8(TextUtil::UTF16ToUTF32(u1, u2));
    return true;
}


// Helper for parseStringConstant; copies a singe Unicode codepoint from ch to s.
// See https://en.wikipedia.org/wiki/UTF-8 in order to understand the implementation.
inline static void UTF8Advance(std::string::const_iterator &ch, std::string * const s) {
    if ((static_cast<unsigned char>(*ch) & 0b10000000u) == 0) { // High bit is not set.
        *s += *ch++;
    } else if ((static_cast<unsigned char>(*ch) & 0b11100000u) == 0b11000000u) {
        *s += *ch++;
        *s += *ch++;
    } else if ((static_cast<unsigned char>(*ch) & 0b11110000u) == 0b11100000u) {
        *s += *ch++;
        *s += *ch++;
        *s += *ch++;
    } else if ((static_cast<unsigned char>(*ch) & 0b11111000u) == 0b11110000u) {
        *s += *ch++;
        *s += *ch++;
        *s += *ch++;
        *s += *ch++;
    }
}


TokenType Scanner::parseStringConstant() {
    ++ch_; // Skip over initial double quote.

    const unsigned start_line_no(line_no_);
    std::string string_value;
    while (ch_ != end_ and *ch_ != '"') {
        if (*ch_ != '\\')
            UTF8Advance(ch_, &string_value);
        else { // Deal w/ an escape sequence.
            if (unlikely(ch_ + 1 == end_)) {
                last_error_message_ = "end-of-input encountered while parsing a string constant, starting on line "
                                      + std::to_string(start_line_no) + "!";
                return ERROR;
            }
            ++ch_;
            switch (*ch_) {
            case '/':
            case '"':
            case '\\':
                string_value += *ch_++;
                break;
            case 'b':
                ++ch_;
                string_value += '\b';
                break;
            case 'f':
                ++ch_;
                string_value += '\f';
                break;
            case 'n':
                ++ch_;
                string_value += '\n';
                break;
            case 'r':
                ++ch_;
                string_value += '\r';
                break;
            case 't':
                ++ch_;
                string_value += '\t';
                break;
            case 'u': {
                ++ch_;
                std::string utf8;
                if (unlikely(not UTF16EscapeToUTF8(&utf8)))
                    return ERROR;
                string_value += utf8;
                break;
            }
            default:
                last_error_message_ = "unexpected escape \\" + std::string(1, *ch_) + " in string constant!";
                return ERROR;
            }
        }
    }

    if (unlikely(ch_ == end_)) {
        last_error_message_ = "end-of-input encountered while parsing a string constant, starting on line "
                              + std::to_string(start_line_no) + "!";
        return ERROR;
    }
    ++ch_; // Skip over closing double quote.

    last_string_constant_ = string_value;
    return STRING_CONST;
}


static std::string EscapeDoubleQuotes(const std::string &unescaped) {
    std::string escaped;
    escaped.reserve(unescaped.length());
    for (const char ch : unescaped) {
        if (ch == '"')
            escaped += "\\\"";
        else
            escaped += ch;
    }

    return escaped;
}


std::string JSONNode::TypeToString(const Type type) {
    switch (type) {
    case BOOLEAN_NODE:
        return "BOOLEAN_NODE";
    case NULL_NODE:
        return "NULL_NODE";
    case STRING_NODE:
        return "STRING_NODE";
    case INT64_NODE:
        return "INT64_NODE";
    case DOUBLE_NODE:
        return "DOUBLE_NODE";
    case OBJECT_NODE:
        return "OBJECT_NODE";
    case ARRAY_NODE:
        return "ARRAY_NODE";
    default:
        throw std::runtime_error("in JSON::JSONNode::TypeToString: we should never get here!");
    };
}


std::string StringNode::toString() const {
    return "\"" + EscapeString(value_) + "\"";
}


ObjectNode::~ObjectNode() {
    for (auto &entry : entries_)
        delete entry.second;
}


ObjectNode *ObjectNode::clone() const {
    ObjectNode *the_clone(new ObjectNode);
    for (const auto &entry : entries_)
        the_clone->entries_[entry.first] = entry.second->clone();

    return the_clone;
}


std::string ObjectNode::toString() const {
    std::string as_string;
    as_string += "{ ";
    for (const auto &entry : entries_) {
        as_string += "\"" + EscapeDoubleQuotes(entry.first) + "\"";
        as_string += ": ";
        as_string += entry.second->toString();
        as_string += ", ";
    }
    if (not entries_.empty())
        as_string.resize(as_string.size() - 2); // Strip off final comma+space.
    as_string += " }";

    return as_string;
}


bool ObjectNode::insert(const std::string &label, JSONNode * const node) {
    if (entries_.find(label) != entries_.end())
        return false;
    entries_.insert(std::make_pair(label, node));

    return true;
}


bool ObjectNode::remove(const std::string &label) {
    const auto entry(entries_.find(label));
    if (entry == entries_.cend())
        return false;
    entries_.erase(entry);
    return true;
}


const JSONNode *ObjectNode::getNode(const std::string &label) const {
    const auto entry(entries_.find(label));
    return entry == entries_.cend() ? nullptr : entry->second;
}


JSONNode *ObjectNode::getNode(const std::string &label) {
    const auto entry(entries_.find(label));
    return entry == entries_.cend() ? nullptr : entry->second;
}


bool ObjectNode::isNullNode(const std::string &label) const {
    const auto entry(entries_.find(label));
    if (unlikely(entry == entries_.cend()))
        ERROR("label \"" + label + "\" not found!");
    return entry->second->getType() == NULL_NODE;
}


ArrayNode::~ArrayNode() {
    for (auto &value : values_)
        delete value;
}


ArrayNode *ArrayNode::clone() const {
    ArrayNode *the_clone(new ArrayNode);
    the_clone->values_.reserve(values_.size());
    for (const auto &node : values_)
        the_clone->values_.emplace_back(node->clone());

    return the_clone;
}


std::string ArrayNode::toString() const {
    std::string as_string;
    as_string += "[ ";
    for (const auto &value : values_) {
        as_string += value->toString();
        as_string += ", ";
    }
    if (not values_.empty())
        as_string.resize(as_string.size() - 2); // Strip off final comma+space.
    as_string += " ]";

    return as_string;
}


bool ArrayNode::isNullNode(const size_t index) const {
    if (unlikely(index >= values_.size()))
        ERROR("index " + std::to_string(index) + " out of range [0," + std::to_string(values_.size()) + ")!");
    return values_[index]->getType() == NULL_NODE;
}


bool Parser::parseObject(JSONNode **new_object_node) {
    *new_object_node = new ObjectNode();
    TokenType token(scanner_.getToken());
    if (unlikely(token == CLOSE_BRACE))
        return true; // We have an empty object.

    for (;;) {
        if (unlikely(token != STRING_CONST)) {
            error_message_ = "label expected on line " + std::to_string(scanner_.getLineNumber())
                             + " found '" + TokenTypeToString(token) + "' instead!";
            return false;
        }
        const std::string label(scanner_.getLastStringConstant());

        token = scanner_.getToken();
        if (unlikely(token != COLON)) {
            error_message_ = "colon expected after label on line " + std::to_string(scanner_.getLineNumber())
                + " found '" + TokenTypeToString(token) + "' instead!";
            return false;
        }

        JSONNode *new_node(nullptr);
        if (unlikely(not parseAny(&new_node))) {
            delete new_node;
            return false;
        }

        reinterpret_cast<ObjectNode *>(*new_object_node)->insert(label, new_node);

        token = scanner_.getToken();
        if (token == COMMA)
            token = scanner_.getToken();
        else if (token == CLOSE_BRACE)
            return true;
        else {
            error_message_ = "expected ',' or '}' on line " + std::to_string(scanner_.getLineNumber())
                             + " but found '" + TokenTypeToString(token) + "!";
            return false;
        }
    }
}


bool Parser::parseArray(JSONNode **new_array_node) {
    *new_array_node = new ArrayNode();
    TokenType token(scanner_.getToken());
    if (unlikely(token == CLOSE_BRACKET))
        return true; // Empty array.
    scanner_.ungetToken(token);

    for (;;) {
        JSONNode *new_node(nullptr);
        if (unlikely(not parseAny(&new_node))) {
            delete new_node;
            return false;
        }
        reinterpret_cast<ArrayNode *>(*new_array_node)->push_back(new_node);

        token = scanner_.getToken();
        if (token == COMMA)
            /* Intentionally empty! */;
        else if (token == CLOSE_BRACKET)
            return true;
        else {
            error_message_ = "expected ',' or ']' on line " + std::to_string(scanner_.getLineNumber())
                             + " but found '" + TokenTypeToString(token) + "!";
            return false;
        }
    }

    return true;
}


bool Parser::parseAny(JSONNode **new_node) {
    *new_node = nullptr;

    TokenType token(scanner_.getToken());
    switch (token) {
    case OPEN_BRACE:
        return parseObject(new_node);
    case OPEN_BRACKET:
        return parseArray(new_node);
    case INTEGER_CONST:
        *new_node = new IntegerNode(scanner_.getLastIntegerConstant());
        return true;
    case DOUBLE_CONST:
        *new_node = new DoubleNode(scanner_.getLastDoubleConstant());
        return true;
    case STRING_CONST:
        *new_node = new StringNode(scanner_.getLastStringConstant());
        return true;
    case TRUE_CONST:
        *new_node = new BooleanNode(true);
        return true;
    case FALSE_CONST:
        *new_node = new BooleanNode(false);
        return true;
    case NULL_CONST:
        *new_node = new NullNode();
        return true;
    case ERROR:
        error_message_ = scanner_.getLastErrorMessage() + "(line: " + std::to_string(scanner_.getLineNumber())
                         + ")";
        return false;
    case END_OF_INPUT:
        error_message_ = "unexpected end of input!";
        return false;
    default:
        error_message_ = "syntax error, found '" + TokenTypeToString(token)
                         + "' but expected some kind of object on line " + std::to_string(scanner_.getLineNumber())
                         + "!";
        return false;
    }
}


bool Parser::parse(JSONNode **tree_root) {
    if (unlikely(not parseAny(tree_root)))
        return false;

    const TokenType token(scanner_.getToken());
    if (likely(token == END_OF_INPUT))
        return true;

    error_message_ = "found trailing garbage " + TokenTypeToString(token) + " on line "
                     + std::to_string(scanner_.getLineNumber()) + "!";
    return false;
}


std::string TokenTypeToString(const TokenType token) {
    switch (token) {
    case COMMA:
        return ",";
    case COLON:
        return ":";
    case OPEN_BRACE:
        return "{";
    case CLOSE_BRACE:
        return "}";
    case OPEN_BRACKET:
        return "[";
    case CLOSE_BRACKET:
        return "]";
    case TRUE_CONST:
        return "true";
    case FALSE_CONST:
        return "false";
    case NULL_CONST:
        return "null";
    case INTEGER_CONST:
        return "integer";
    case DOUBLE_CONST:
        return "double";
    case STRING_CONST:
        return "string";
    case END_OF_INPUT:
        return "end-of-input";
    case ERROR:
        return "error";
    }

    #ifdef __GNUC__
        #if __GNUC__ > 4 || (__GNUC__ == 3 && __GNUC_MINOR__ >= 5)
            __builtin_unreachable();
        #endif
    #endif
}


static size_t ParsePath(const std::string &path, std::vector<std::string> * const components) {
    std::string component;

    if (not StringUtil::StartsWith(path, "/"))
        throw std::runtime_error("in JSON::ParsePath: path must start with a slash!");
    bool escaped(false);
    for (const char ch : path.substr(1)) {
        if (escaped) {
            component += ch;
            escaped = false;
        } else if (ch == '\\')
            escaped = true;
        else if (ch == '/') {
            if (unlikely(component.empty()))
                throw std::runtime_error("in JSON::ParsePath: detected an empty path component!");
            components->emplace_back(component);
            component.clear();
        } else
            component += ch;
    }

    if (not component.empty())
        components->emplace_back(component);

    return components->size();
}


static const JSONNode *GetLastPathComponent(const std::string &path, const JSONNode * const tree,
                                            const bool have_default)
{
    std::vector<std::string> path_components;
    if (unlikely(ParsePath(path, &path_components) == 0))
        throw std::runtime_error("in JSON::GetLastPathComponent: an empty path is invalid!");

    const JSONNode *next_node(tree);
    for (const auto &path_component : path_components) {
        if (next_node == nullptr) {
            if (unlikely(not have_default))
                throw std::runtime_error("in JSON::GetLastPathComponent: can't find \"" + path
                                         + "\" in our JSON tree!");
            return nullptr;
        }

        switch (next_node->getType()) {
        case JSONNode::BOOLEAN_NODE:
        case JSONNode::NULL_NODE:
        case JSONNode::STRING_NODE:
        case JSONNode::INT64_NODE:
        case JSONNode::DOUBLE_NODE:
            throw std::runtime_error("in JSON::GetLastPathComponent: can't descend into a scalar node!");
        case JSONNode::OBJECT_NODE:
            next_node = reinterpret_cast<const ObjectNode *>(next_node)->getNode(path_component);
            if (next_node == nullptr) {
                if (unlikely(not have_default))
                    throw std::runtime_error("in JSON::GetLastPathComponent: can't find path component \""
                                             + path_component + "\" in path \"" + path + "\" in our JSON tree!");
                return nullptr;
            }
            break;
        case JSONNode::ARRAY_NODE:
            unsigned index;
            if (unlikely(not StringUtil::ToUnsigned(path_component, &index)))
                throw std::runtime_error("in JSON::GetLastPathComponent: path component \"" + path_component
                                         + "\" in path \"" + path + "\" can't be converted to an array index!");
            const ArrayNode * const array_node(reinterpret_cast<const ArrayNode *>(next_node));
            if (unlikely(index >= array_node->size()))
                throw std::runtime_error("in JSON::GetLastPathComponent: path component \"" + path_component
                                         + "\" in path \"" + path + "\" is too large as an array index!");
            next_node = array_node->getNode(index);
            break;
        }
    }

    return next_node;
}


static std::string LookupString(const std::string &path, const JSONNode * const tree,
                                const std::string &default_value, const bool use_default_value)
{
    const JSONNode * const bottommost_node(GetLastPathComponent(path, tree, use_default_value));
    if (bottommost_node == nullptr)
        return default_value;

    switch (bottommost_node->getType()) {
    case JSONNode::BOOLEAN_NODE:
        return reinterpret_cast<const BooleanNode *>(bottommost_node)->getValue() ? "true" : "false";
    case JSONNode::NULL_NODE:
        return "null";
    case JSONNode::STRING_NODE:
        return reinterpret_cast<const StringNode *>(bottommost_node)->getValue();
    case JSONNode::INT64_NODE:
        return std::to_string(reinterpret_cast<const IntegerNode *>(bottommost_node)->getValue());
    case JSONNode::DOUBLE_NODE:
        return std::to_string(reinterpret_cast<const DoubleNode *>(bottommost_node)->getValue());
    case JSONNode::OBJECT_NODE:
        throw std::runtime_error("in JSON::LookupString: can't get a unique value from an object node!");
    case JSONNode::ARRAY_NODE:
        throw std::runtime_error("in JSON::LookupString: can't get a unique value from an array node!");
    }

    #ifdef __GNUC__
        #if __GNUC__ > 4 || (__GNUC__ == 3 && __GNUC_MINOR__ >= 5)
            __builtin_unreachable();
        #endif
    #endif
}


std::string LookupString(const std::string &path, const JSONNode * const tree) {
    return LookupString(path, tree, "", /* use_default_value = */ false);
}


std::string LookupString(const std::string &path, const JSONNode * const tree, const std::string &default_value) {
    return LookupString(path, tree, default_value, /* use_default_value = */ true);
}


static int64_t LookupInteger(const std::string &path, const JSONNode * const tree, const int64_t default_value,
                             const bool use_default_value)
{
    const JSONNode * const bottommost_node(GetLastPathComponent(path, tree, use_default_value));
    if (bottommost_node == nullptr)
        return default_value;

    switch (bottommost_node->getType()) {
    case JSONNode::BOOLEAN_NODE:
        throw std::runtime_error("in JSON::LookupInteger: can't convert a boolean value to an integer!");
    case JSONNode::NULL_NODE:
        throw std::runtime_error("in JSON::LookupInteger: can't convert \"null\" to an integer!");
    case JSONNode::STRING_NODE:
        throw std::runtime_error("in JSON::LookupInteger: can't convert a string value to an integer!");
    case JSONNode::INT64_NODE:
        return reinterpret_cast<const IntegerNode *>(bottommost_node)->getValue();
    case JSONNode::DOUBLE_NODE:
        throw std::runtime_error("in JSON::LookupInteger: can't convert a double value to an integer!");
    case JSONNode::OBJECT_NODE:
        throw std::runtime_error("in JSON::LookupInteger: can't get a unique value from an object node!");
    case JSONNode::ARRAY_NODE:
        throw std::runtime_error("in JSON::LookupInteger: can't get a unique value from an array node!");
    }

    #ifdef __GNUC__
        #if __GNUC__ > 4 || (__GNUC__ == 3 && __GNUC_MINOR__ >= 5)
            __builtin_unreachable();
        #endif
    #endif
}


int64_t LookupInteger(const std::string &path, const JSONNode * const tree) {
    return LookupInteger(path, tree, 0L, /* use_default_value = */ false);
}


int64_t LookupInteger(const std::string &path, const JSONNode * const tree, const int64_t default_value) {
    return LookupInteger(path, tree, default_value, /* use_default_value = */ true);
}


std::string EscapeString(const std::string &unescaped_string) {
    std::string escaped_string;
    for (const char ch : unescaped_string) {
        if (static_cast<unsigned char>(ch) <= 0x1Fu) { // Escape control characters.
            escaped_string += "\\x";
            escaped_string += StringUtil::ToHex(static_cast<unsigned char>(ch) >> 4u);
            escaped_string += StringUtil::ToHex(static_cast<unsigned char>(ch) & 0xFu);
        } else {
            switch (ch) {
            case '\\':
                escaped_string += "\\\\";
                break;
            case '"':
                escaped_string += "\\\"";
                break;
            case '/':
                escaped_string += "\\/";
                break;
            case '\b':
                escaped_string += "\\b";
                break;
            case '\f':
                escaped_string += "\\f";
                break;
            case '\n':
                escaped_string += "\\n";
                break;
            case '\r':
                escaped_string += "\\r";
                break;
            case '\t':
                escaped_string += "\\t";
                break;
            default:
                escaped_string += ch;
            }
        }
    }

    return escaped_string;
}


} // namespace JSON
