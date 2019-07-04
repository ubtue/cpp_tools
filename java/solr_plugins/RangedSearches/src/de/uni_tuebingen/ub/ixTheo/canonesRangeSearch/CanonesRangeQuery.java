package de.uni_tuebingen.ub.ixTheo.canonesRangeSearch;


import org.apache.lucene.search.IndexSearcher;
import org.apache.lucene.search.Query;
import org.apache.lucene.search.Weight;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import java.io.IOException;
import java.util.Arrays;
import de.uni_tuebingen.ub.ixTheo.rangeSearch.Range;
import de.uni_tuebingen.ub.ixTheo.rangeSearch.RangeQuery;


class CanonesRangeQuery extends RangeQuery {
    CanonesRangeQuery(final Query query, final CanonesRange[] ranges) {
        super(query, Arrays.copyOf(ranges, ranges.length, Range[].class));
    }

    @Override
    public Weight createWeight(final IndexSearcher searcher, final boolean needsScores, final float boost) throws IOException {
        return new CanonesRangeWeight(this, Arrays.copyOf(ranges, ranges.length, CanonesRange[].class),
                                    super.createWeight(searcher, needsScores, boost));
    }

    @Override
    public boolean equals(final Object obj) {
        if (!(obj instanceof CanonesRangeQuery))
            return false;

        return super.equals(obj);
    }
}
