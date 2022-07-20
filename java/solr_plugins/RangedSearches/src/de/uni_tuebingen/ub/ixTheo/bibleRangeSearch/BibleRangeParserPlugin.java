package de.uni_tuebingen.ub.ixTheo.bibleRangeSearch;


import org.apache.solr.common.params.SolrParams;
import org.apache.solr.common.util.NamedList;
import org.apache.solr.request.SolrQueryRequest;
import org.apache.solr.search.QParser;
import org.apache.solr.search.QParserPlugin;


public class BibleRangeParserPlugin extends QParserPlugin {

    @Override
    @SuppressWarnings("rawtypes")
    public void init(final NamedList args) {
    }

    @Override
    public QParser createParser(final String queryString, final SolrParams localParams, final SolrParams params, final SolrQueryRequest req) {
        return new BibleRangeParser(queryString, localParams, params, req);
    }
}
