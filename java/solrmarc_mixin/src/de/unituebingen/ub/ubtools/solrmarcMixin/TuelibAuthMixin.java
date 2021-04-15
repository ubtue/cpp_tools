package de.unituebingen.ub.ubtools.solrmarcMixin;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.logging.Logger;
import org.marc4j.marc.DataField;
import org.marc4j.marc.Record;
import org.solrmarc.index.SolrIndexerMixin;

public class TuelibAuthMixin extends SolrIndexerMixin {

    protected final static Logger logger = Logger.getLogger(TuelibAuthMixin.class.getName());

    /**
     * normalize string due to specification for isni or orcid
     * @param input    input string to normalize
     * @param category category isni or orchid
     * @return normalized value depending on isni, orcid pattern
     */
    private String normalizeByCategory(String input, String category) {
        String stripped = stripDashesAndWhitespaces(input);
        if (stripped.length() != 16) {
            return input;
        } else {
            if (category.equalsIgnoreCase("isni")) {
                return stripped.substring(0, 4) + " " + stripped.substring(4, 8) + " " + stripped.substring(8, 12) + " " + stripped.substring(12, 16);
            } else if (category.equalsIgnoreCase("orcid")) {
                return stripped.substring(0, 4) + "-" + stripped.substring(4, 8) + "-" + stripped.substring(8, 12) + "-" + stripped.substring(12, 16);
            } else {
                return input;
            }
        }
    }

    private String stripDashesAndWhitespaces(String input) {
        return input.replaceAll("-", "").replaceAll("\\s", "");
    }

    /**
     * @param record          implicit call
     * @param tagNumber       e.g. 024, only use Datafields > 010
     * @param number2Category isni | orcid
     * @return
     */
    public String getNormalizedValueByTag2(final Record record, final String tagNumber, final String number2Category) {

        List<DataField> mainFields = (List<DataField>) (List<?>) record.getVariableFields(tagNumber);
        mainFields.removeIf(m -> m.getSubfield('2') == null);
        mainFields.removeIf(m -> m.getSubfield('a') == null);
        mainFields.removeIf(m -> m.getSubfield('2').getData().equalsIgnoreCase(number2Category) == false);

        if (mainFields.size() == 0) {
            return null;
        } else if (mainFields.size() == 1) {
            return normalizeByCategory(mainFields.get(0).getSubfield('a').getData(), number2Category);
        } else {
            Set<String> differentNormalizedValues = new HashSet<String>();
            for (DataField mainField : mainFields) {
                final String numberA = mainField.getSubfield('a').getData();
                String normalizedValue = normalizeByCategory(numberA, number2Category);
                differentNormalizedValues.add(normalizedValue);
            }
            if (differentNormalizedValues.size() == 1) {
                return differentNormalizedValues.iterator().next();
            } else {
                logger.warning("record id " + record.getControlNumber() + " - multiple field with different content " + number2Category);
                return null;
            }

        }
    }
}
