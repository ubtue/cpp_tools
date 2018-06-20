package de.uni_tuebingen.ub.ixTheo.multiLanguageQuery;

import java.util.ArrayList;
import java.io.IOException;
import java.util.Iterator;
import java.util.Set;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.apache.commons.lang.ArrayUtils;
import org.apache.commons.lang.StringUtils;
import org.apache.lucene.index.Term;
import org.apache.lucene.search.BooleanClause;
import org.apache.lucene.search.BooleanQuery;
import org.apache.lucene.search.BoostQuery;
import org.apache.lucene.search.DisjunctionMaxQuery;
import org.apache.lucene.search.MultiPhraseQuery;
import org.apache.lucene.search.MatchAllDocsQuery;
import org.apache.lucene.search.PhraseQuery;
import org.apache.lucene.search.PrefixQuery;
import org.apache.lucene.search.Query;
import org.apache.lucene.search.TermQuery;
import org.apache.lucene.search.TermRangeQuery;
import org.apache.lucene.search.WildcardQuery;
import org.apache.solr.common.params.SolrParams;
import org.apache.solr.common.params.ModifiableSolrParams;
import org.apache.solr.common.SolrException;
import org.apache.solr.common.SolrException.ErrorCode;
import org.apache.solr.query.SolrRangeQuery;
import org.apache.solr.request.SolrQueryRequest;
import org.apache.solr.schema.IndexSchema;
import org.apache.solr.search.DisMaxQParser;
import org.apache.solr.search.ExtendedDismaxQParser;
import org.apache.solr.search.LuceneQParser;
import org.apache.solr.search.QParser;
import org.apache.solr.search.SyntaxError;
import org.apache.solr.servlet.SolrRequestParsers;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


public class MultiLanguageQueryParser extends QParser {
    private String searchString;
    private static Logger logger = LoggerFactory.getLogger(MultiLanguageQueryParser.class);
    private String[] SUPPORTED_LANGUAGES = { "de", "en", "fr", "it", "es", "hant", "hans", "pt", "ru", "el" };
    private SolrQueryRequest newRequest;
    private ModifiableSolrParams newParams;
    private IndexSchema schema;
    private String lang;
    private Query newQuery;
    private Pattern LOCAL_PARAMS_PATTERN = Pattern.compile("(\\{![^}]*\\})");


    public MultiLanguageQueryParser(final String searchString, final SolrParams localParams, final SolrParams params,
            final SolrQueryRequest request) throws MultiLanguageQueryParserException
    {
        super(searchString, localParams, params, request);
        this.searchString = searchString;
        newRequest = request;
        this.newParams = new ModifiableSolrParams();
        this.newParams.add(params);
        schema = request.getSchema();
        Boolean useDismax = false;
        String[] query = newParams.getParams("q");
        String[] queryFields = null;

        // Check whether we have dismax or edismax
        String[] queryType = newParams.getParams("qt");
        if (queryType != null) {
            queryFields = newParams.getParams("qf");
            useDismax = true;
        } else if (query.length != 1)
            throw new MultiLanguageQueryParserException("Only one q-parameter is supported");

        String[] facetFields = newParams.getParams("facet.field");

        lang = newParams.get("lang", "de");

        // Strip language subcode
        lang = lang.split("-")[0];

        // Set default language if we do not directly support the chosen
        // language
        lang = ArrayUtils.contains(SUPPORTED_LANGUAGES, lang) ? lang : "de";

        // Handle Facet Fields
        if (facetFields != null && facetFields.length > 0) {
            for (String param : facetFields) {
                String fieldLocalParams = extractLocalParams(param);
                String strippedParam = stripLocalParams(param);
                // Replace field used if it exists
                String newFieldName = strippedParam + "_" + lang;
                if (schema.getFieldOrNull(newFieldName) != null) {
                    newParams.remove("facet.field", param);
                    String newLocalParams = "";
                    // Skip renaming the returned field names if we have prefix sorting for facets
                    if (!newParams.get("facet.sort").equals("prefix")) {
                        newLocalParams = fieldLocalParams.equals("") ?  "{!key=" + strippedParam + "}" :
                                            fieldLocalParams.replace("}", " key=" + strippedParam + "}");
                    }
                    newParams.add("facet.field", newLocalParams + newFieldName);
                }
            }
            this.newRequest.setParams(newParams);
        }


        // Handle filter queries
        final String[] filterQueries = newParams.getParams("fq");
        if (filterQueries != null && filterQueries.length > 0) {
            for (final String filterQuery : filterQueries) {
                final String[] fieldNameAndFilterValues = filterQuery.split(":");
                final int fieldNameAndFilterValuesLength = fieldNameAndFilterValues.length;
                // The usual case is an ordinary expression made up of a field + ":" + query
                // Moreover, we can have complex (i.e. parenthesized) expressions on the right hand side
                // so we try to replace any field left to a colon
                if (fieldNameAndFilterValuesLength >= 2) {
                    String newFilterQuery = new String();
                    for (int i = 0; i < fieldNameAndFilterValuesLength - 1; ++i) {
                         final String newFieldExpression = fieldNameAndFilterValues[i] + "_" + lang;
                         //Strip potential local parameters or a leading opening bracket of any tokens to the left
                         final String newFieldName = newFieldExpression.replaceAll("(\\{.*\\}|^\\(|.*\\s+)", "");
                         if (schema.getFieldOrNull(newFieldName) != null)
                             newFilterQuery += newFieldExpression + ":";
                         else
                             newFilterQuery += fieldNameAndFilterValues[i] + ":";
                    }
                    newFilterQuery += fieldNameAndFilterValues[fieldNameAndFilterValuesLength - 1];
                    newParams.remove("fq", filterQuery);
                    newParams.add("fq", newFilterQuery);
                } else
                    throw new MultiLanguageQueryParserException("Cannot appropriately rewrite " + filterQuery);
            }
        }

        // Handling for [e]dismax
        if (useDismax)
            handleDismaxParser(queryFields, lang, schema);
        // Support for Lucene parser
        else
            handleLuceneParser(query, request, lang, schema);
    }


    /*
     * Extract LocalParams, i.e. parameters in square brackets
     */
    private String extractLocalParams(String param) {
        Matcher matcher = LOCAL_PARAMS_PATTERN.matcher(param);
        return matcher.find() ? matcher.group() : "";
    }


    /*
     * Strip local params
     */
    private String stripLocalParams(String param) {
        return LOCAL_PARAMS_PATTERN.matcher(param).replaceAll("");
    }


    private void handleDismaxParser(String[] queryFields, String lang, IndexSchema schema) {
        StringBuilder stringBuilder = new StringBuilder();
        // Only replace parameters if qf is indeed set
        if (newParams.get("qf") == null)
            return;
        for (final String param : queryFields) {
            newParams.remove("qf", param);
            String[] singleParams = param.split(" ");
            int i = 0;
            for (final String singleParam : singleParams) {
                String newFieldName = singleParam + "_" + lang;
                newFieldName = (schema.getFieldOrNull(newFieldName) != null) ? newFieldName : singleParam;
                stringBuilder.append(newFieldName);
                if (++i < singleParams.length)
                    stringBuilder.append(" ");
            }
         }
         newParams.add("qf", stringBuilder.toString());
         try {
             this.newRequest.setParams(newParams);
             QParser parser = getParser(this.searchString, "edismax", this.newRequest);
             newQuery = parser.parse();
         } catch (SyntaxError e) {
               throw new SolrException(ErrorCode.SERVER_ERROR, "Could not succesfully rewrite query", e);
         }
    }


    private Query processTermQuery(TermQuery termQuery) {
        final String field = termQuery.getTerm().field();
        final String newFieldName = field + "_" + lang;
        if (schema.getFieldOrNull(newFieldName) != null)
            return new TermQuery(new Term(newFieldName, termQuery.getTerm().text()));
        else
            return new TermQuery(new Term(field, termQuery.getTerm().text()));
    }


    private Query processPhraseQuery(final PhraseQuery queryCandidate) {
        final PhraseQuery.Builder phraseQueryBuilder = new PhraseQuery.Builder();
        for (final Term term : queryCandidate.getTerms()) {
            final String newFieldName = term.field() + "_" + lang;
            if (schema.getFieldOrNull(newFieldName) != null)
                phraseQueryBuilder.add(new Term(newFieldName, term.text()));
            else
                phraseQueryBuilder.add(term);
        }

        phraseQueryBuilder.setSlop(queryCandidate.getSlop());
        return phraseQueryBuilder.build();
    }


    private Query processMultiPhraseQuery(final MultiPhraseQuery queryCandidate) {
       final MultiPhraseQuery.Builder multiPhraseQueryBuilder = new MultiPhraseQuery.Builder();
       for (final Term[] termArray : queryCandidate.getTermArrays()) {
           int arrayOffset = 0;
           for (final Term term : termArray) {
               String newFieldName = term.field() + "_" + lang;
               if (schema.getFieldOrNull(newFieldName) != null)
                  termArray[arrayOffset] = new Term(newFieldName, term.text());
               else
                  termArray[arrayOffset] = term;
               ++arrayOffset;
           }
           multiPhraseQueryBuilder.add(termArray);
       }
       multiPhraseQueryBuilder.setSlop(queryCandidate.getSlop());
       return multiPhraseQueryBuilder.build();
    }


    private Query processDisjunctionMaxQuery(DisjunctionMaxQuery queryCandidate) {
        final List<Query> queryList = new ArrayList<Query>();
        final DisjunctionMaxQuery disjunctionMaxQuery = (DisjunctionMaxQuery) queryCandidate;
        for (Query currentClause : disjunctionMaxQuery.getDisjuncts()) {
             if (currentClause instanceof BoostQuery)
                 currentClause = processBoostQuery((BoostQuery)currentClause);
             else if (currentClause instanceof TermQuery)
                 currentClause = processTermQuery((TermQuery)currentClause);
             else if (currentClause instanceof BooleanQuery)
                 currentClause = processBooleanQuery((BooleanQuery)currentClause);
             else if (currentClause instanceof PhraseQuery)
                 currentClause = processPhraseQuery((PhraseQuery)currentClause);
             else
                 throw new SolrException(ErrorCode.SERVER_ERROR, "Unknown currentClause type in DisjunctionMaxQuery: " +
                                         currentClause.getClass().getName());

             queryList.add(currentClause);
        }
        return new DisjunctionMaxQuery(queryList, queryCandidate.getTieBreakerMultiplier());
    }


    private Query processBoostQuery(final BoostQuery queryCandidate) {
        Query subquery = queryCandidate.getQuery();
        if (subquery instanceof TermQuery) {
            subquery = processTermQuery((TermQuery)subquery);
            return new BoostQuery(subquery, queryCandidate.getBoost());
        } else if (subquery instanceof BooleanQuery) {
            subquery = processBooleanQuery((BooleanQuery)subquery);
            return new BoostQuery(subquery, queryCandidate.getBoost());
        } else if (subquery instanceof PrefixQuery) {
            subquery = processPrefixQuery((PrefixQuery)subquery);
            return new BoostQuery(subquery, queryCandidate.getBoost());
        } else if (subquery instanceof PhraseQuery) {
            subquery = processPhraseQuery((PhraseQuery)subquery);
            return new BoostQuery(subquery, queryCandidate.getBoost());
        } else if (subquery instanceof MultiPhraseQuery) {
            subquery = processMultiPhraseQuery((MultiPhraseQuery)subquery);
            return new BoostQuery(subquery, queryCandidate.getBoost());
        } else if (subquery instanceof WildcardQuery) {
            subquery = processWildcardQuery((WildcardQuery)subquery);
            return new BoostQuery(subquery, queryCandidate.getBoost());
        } else
	    throw new SolrException(ErrorCode.SERVER_ERROR, "Boost Query: Unable to handle " +  subquery.getClass().getName());
    }


    private Query processPrefixQuery(final PrefixQuery queryCandidate) {
        final Term term = queryCandidate.getPrefix();
        final TermQuery newTermQuery = (TermQuery)processTermQuery(new TermQuery(term));
        return new PrefixQuery(new Term(newTermQuery.getTerm().field(), newTermQuery.getTerm().text()));
    }


    private Query processWildcardQuery(final WildcardQuery queryCandidate) {
        final Term term = queryCandidate.getTerm();
        final TermQuery newTermQuery = (TermQuery)processTermQuery(new TermQuery(term));
        return new WildcardQuery(new Term(newTermQuery.getTerm().field(), newTermQuery.getTerm().text()));
    }


    private Query processBooleanQuery(final BooleanQuery queryCandidate) {
        if (!(queryCandidate instanceof BooleanQuery))
             throw new SolrException(ErrorCode.SERVER_ERROR, "Argument is not a BooleanQuery");
        final BooleanQuery.Builder queryBuilder = new BooleanQuery.Builder();
        for (final BooleanClause currentClause : queryCandidate.clauses()) {
            Query subquery = currentClause.getQuery();
            if (subquery instanceof TermQuery) {
                subquery = processTermQuery((TermQuery)subquery);
            } else if (subquery instanceof DisjunctionMaxQuery) {
                subquery = processDisjunctionMaxQuery((DisjunctionMaxQuery)subquery);
            } else if (subquery instanceof BoostQuery) {
                subquery = processBoostQuery((BoostQuery)subquery);
            } else if (subquery instanceof BooleanQuery) {
                subquery = processBooleanQuery((BooleanQuery)subquery);
            } else if (subquery instanceof PrefixQuery) {
                subquery = processPrefixQuery((PrefixQuery)subquery);
            } else if (subquery instanceof PhraseQuery) {
                subquery = processPhraseQuery((PhraseQuery)subquery);
            } else if (subquery instanceof MultiPhraseQuery) {
                subquery = processMultiPhraseQuery((MultiPhraseQuery)subquery);
            } else
                logger.warn("No appropriate Query in BooleanClause for " + subquery.getClass().getName());
            queryBuilder.add(subquery, currentClause.getOccur());
       }
       return queryBuilder.build();
    }


    private Query processTermRangeQuery(final TermRangeQuery queryCandidate) {
        String field = queryCandidate.getField();
        String newFieldName = field + "_" + lang;
        if (schema.getFieldOrNull(newFieldName) != null) {
            return new TermRangeQuery(newFieldName,
                                      queryCandidate.getLowerTerm(),
                                      queryCandidate.getUpperTerm(),
                                      queryCandidate.includesLower(),
                                      queryCandidate.includesUpper());
        }
        return queryCandidate;
    }


    private Query processSolrRangeQuery(final SolrRangeQuery queryCandidate) {
        String field = queryCandidate.getField();
        String newFieldName = field + "_" + lang;
        // There does not seem to a proper way to get Upper and Lower Terms of a SolrRangeQuery
        // without reparsing. Moreover the SolrRangeQuery API is experimental
        // Range Queries only make sense in the context of numeric fields
        // which are language independent, so in practice there should never the need to rewrite
        // So throw an exception if we really encounter this esoteric case
        if (schema.getFieldOrNull(newFieldName) != null) {
            throw new SolrException(ErrorCode.SERVER_ERROR, "Language dependent SolrRangeQueries are currently not supported");
        }
        return queryCandidate;
    }


    private Query processMatchAllDocsQuery(final MatchAllDocsQuery queryCandidate) {
        //Since all docs are matched, no modifications are needed
        return queryCandidate;
    }


    private void handleLuceneParser(String[] query, SolrQueryRequest request, String lang, IndexSchema schema) throws MultiLanguageQueryParserException {
        if (query.length != 1)
           throw new MultiLanguageQueryParserException("Only one q-parameter is supported [1]");

        try {
            QParser tmpParser = new ExtendedDismaxQParser(searchString, localParams, newParams, this.newRequest);
            newQuery = tmpParser.getQuery();
            newQuery = newQuery.rewrite(request.getSearcher().getIndexReader());
            if (newQuery instanceof BooleanQuery)
                newQuery = processBooleanQuery((BooleanQuery)newQuery);
            else if (newQuery instanceof TermRangeQuery)
                newQuery = processTermRangeQuery((TermRangeQuery)newQuery);
            else if (newQuery instanceof TermQuery)
                newQuery = processTermQuery((TermQuery)newQuery);
            else if (newQuery instanceof DisjunctionMaxQuery)
                newQuery = processDisjunctionMaxQuery((DisjunctionMaxQuery)newQuery);
            else if (newQuery instanceof BoostQuery)
                newQuery = processBoostQuery((BoostQuery)newQuery);
            else if (newQuery instanceof MatchAllDocsQuery)
                newQuery = processMatchAllDocsQuery((MatchAllDocsQuery)newQuery);
            else if (newQuery instanceof SolrRangeQuery)
                newQuery = processSolrRangeQuery((SolrRangeQuery)newQuery);
            else
                logger.warn("No rewrite rule did match for " + newQuery.getClass());
            this.searchString = newQuery.toString();
        } catch (SyntaxError|IOException e) {
            throw new SolrException(ErrorCode.SERVER_ERROR, "Rewriting Lucene support for new languages failed", e);
        }
    }


    public Query parse() throws SyntaxError {
        if (newQuery == null) {
           this.newRequest.setParams(newParams);
           QParser parser = getParser(this.searchString, "edismax", this.newRequest);
           return parser.parse();
        }
        return newQuery;
    }
}

