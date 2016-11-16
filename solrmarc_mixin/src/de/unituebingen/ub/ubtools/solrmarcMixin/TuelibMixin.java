package de.unituebingen.ub.ubtools.solrmarcMixin;


import org.marc4j.marc.DataField;
import org.marc4j.marc.Record;
import org.marc4j.marc.Subfield;
import org.marc4j.marc.VariableField;
import org.solrmarc.index.SolrIndexer;
import org.solrmarc.index.SolrIndexerMixin;
import org.solrmarc.index.SolrIndexerShim;
import org.solrmarc.tools.Utils;

import java.util.*;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;


public class TuelibMixin extends SolrIndexerMixin {
    private final static Logger logger = Logger.getLogger(TuelibMixin.class.getName());
    /**
     * Returns either a Set<String> of parent (URL + colon + material type).  URLs are taken from 856$u and material
     * types from 856$3, 856$z or 856$x.  For missing type subfields the text "Unbekanntes Material" will be used.
     * Furthermore 024$2 will be checked for "doi".  If we find this we generate a URL with a DOI resolver from the
     * DOI in 024$a and set the "material type" to "DOI Link".
     *
     * @param record the record
     * @return A, possibly empty, Set<String> containing the URL/material-type pairs.
     */
    private final static String UNKNOWN_MATERIAL_TYPE = "Unbekanntes Material";
    private final static Pattern EXTRACTION_PATTERN = Pattern.compile("^\\([^)]+\\)(.+)$");
    // TODO: This should be in a translation mapping file
    private final static HashMap<String, String> isil_to_department_map = new HashMap<String, String>() {
        {
            this.put("Unknown", "Unknown");
            this.put("DE-21", "Universit\u00E4tsbibliothek T\u00FCbingen");
            this.put("DE-21-1", "Universit\u00E4t T\u00FCbingen, Klinik f\u00FCr Psychatrie und Psychologie");
            this.put("DE-21-3", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Toxikologie und Pharmakologie");
            this.put("DE-21-4", "Universit\u00E4t T\u00FCbingen, Universit\u00E4ts-Augenklinik");
            this.put("DE-21-10", "Universit\u00E4tsbibliothek T\u00FCbingen, Bereichsbibliothek Geowissenschaften");
            this.put("DE-21-11", "Universit\u00E4tsbibliothek T\u00FCbingen, Bereichsbibliothek Schloss Nord");
            this.put("DE-21-14", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Ur- und Fr\u00FChgeschichte und Arch\u00E4ologie des Mittelalters, Abteilung j\u00FCngere Urgeschichte und Fr\u00FChgeschichte + Abteilung f\u00FCr Arch\u00E4ologie des Mittelalters");
            this.put("DE-21-17", "Universit\u00E4t T\u00FCbingen, Geographisches Institut");
            this.put("DE-21-18", "Universit\u00E4t T\u00FCbingen, Universit\u00E4ts-Hautklinik");
            this.put("DE-21-19", "Universit\u00E4t T\u00FCbingen, Wirtschaftswissenschaftliches Seminar");
            this.put("DE-21-20", "Universit\u00E4t T\u00FCbingen, Frauenklinik");
            this.put("DE-21-21", "Universit\u00E4t T\u00FCbingen, Universit\u00E4ts-Hals-Nasen-Ohrenklinik, Bibliothek");
            this.put("DE-21-22", "Universit\u00E4t T\u00FCbingen, Kunsthistorisches Institut");
            this.put("DE-21-23", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Pathologie");
            this.put("DE-21-24", "Universit\u00E4t T\u00FCbingen, Juristisches Seminar");
            this.put("DE-21-25", "Universit\u00E4t T\u00FCbingen, Musikwissenschaftliches Institut");
            this.put("DE-21-26", "Universit\u00E4t T\u00FCbingen, Anatomisches Institut");
            this.put("DE-21-27", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Anthropologie und Humangenetik");
            this.put("DE-21-28", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Astronomie und Astrophysik, Abteilung Astronomie");
            this.put("DE-21-31", "Universit\u00E4t T\u00FCbingen, Evangelisch-theologische Fakult\u00E4t");
            this.put("DE-21-32a", "Universit\u00E4t T\u00FCbingen, Historisches Seminar, Abteilung f\u00FCr Alte Geschichte");
            this.put("DE-21-32b", "Universit\u00E4t T\u00FCbingen, Historisches Seminar, Abteilung f\u00FCr Mittelalterliche Geschichte");
            this.put("DE-21-32c", "Universit\u00E4t T\u00FCbingen, Historisches Seminar, Abteilung f\u00FCr Neuere Geschichte");
            this.put("DE-21-34", "Universit\u00E4t T\u00FCbingen, Asien-Orient-Institut, Abteilung f\u00FCr Indologie und Vergleichende Religionswissenschaft");
            this.put("DE-21-35", "Universit\u00E4t T\u00FCbingen, Katholisch-theologische Fakult\u00E4t");
            this.put("DE-21-39", "Universit\u00E4t T\u00FCbingen, Fachbibliothek Mathematik und Physik / Bereich Mathematik");
            this.put("DE-21-37", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Sportwissenschaft");
            this.put("DE-21-42", "Universit\u00E4t T\u00FCbingen, Asien-Orient-Institut, Abteilung f\u00FCr Orient- uns Islamwissenschaft");
            this.put("DE-21-43", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Erziehungswissenschaft");
            this.put("DE-21-45", "Universit\u00E4t T\u00FCbingen, Philologisches Seminar");
            this.put("DE-21-46", "Universit\u00E4t T\u00FCbingen, Philosophisches Seminar");
            this.put("DE-21-50", "Universit\u00E4t T\u00FCbingen, Physiologisches Institut");
            this.put("DE-21-51", "Universit\u00E4t T\u00FCbingen, Psychologisches Institut");
            this.put("DE-21-52", "Universit\u00E4t T\u00FCbingen, Ludwig-Uhland-Institut f\u00FCr Empirische Kulturwissenschaft");
            this.put("DE-21-53", "Universit\u00E4t T\u00FCbingen, Asien-Orient-Institut, Abteilung f\u00FCr Ethnologie");
            this.put("DE-21-54", "Universit\u00E4t T\u00FCbingen, Universit\u00E4tsklinik f\u00FCr Zahn-, Mund- und Kieferheilkunde");
            this.put("DE-21-58", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Politikwissenschaft");
            this.put("DE-21-62", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Osteurop\u00E4ische Geschichte und Landeskunde");
            this.put("DE-21-63", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Tropenmedizin");
            this.put("DE-21-64", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Geschichtliche Landeskunde und Historische Hilfswissenschaften");
            this.put("DE-21-65", "Universit\u00E4t T\u00FCbingen, Universit\u00E4ts-Apotheke");
            this.put("DE-21-74", "Universit\u00E4t T\u00FCbingen, Zentrum f\u00FCr Informations-Technologie");
            this.put("DE-21-78", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Medizinische Biometrie");
            this.put("DE-21-81", "Universit\u00E4t T\u00FCbingen, Inst. f. Astronomie und Astrophysik/Abt. Geschichte der Naturwiss.");
            this.put("DE-21-85", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Soziologie");
            this.put("DE-21-86", "Universit\u00E4t T\u00FCbingen, Zentrum f\u00FCr Datenverarbeitung");
            this.put("DE-21-89", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Arbeits- und Sozialmedizin");
            this.put("DE-21-92", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Gerichtliche Medizin");
            this.put("DE-21-93", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Ethik und Geschichte der Medizin");
            this.put("DE-21-95", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Hirnforschung");
            this.put("DE-21-98", "Universit\u00E4t T\u00FCbingen, Fachbibliothek Mathematik und Physik / Bereich Physik");
            this.put("DE-21-99", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Ur- und Fr\u00FChgeschichte und Arch\u00E4ologie des Mittelalters, Abteilung f\u00FCr \u00E4ltere Urgeschichteund Quart\u00E4r\u00F6kologie");
            this.put("DE-21-106", "Universit\u00E4t T\u00FCbingen, Seminar f\u00FCr Zeitgeschichte");
            this.put("DE-21-108", "Universit\u00E4t T\u00FCbingen, Fakult\u00E4tsbibliothek Neuphilologie");
            this.put("DE-21-109", "Universit\u00E4t T\u00FCbingen, Asien-Orient-Institut, Abteilung f\u00FCr Sinologie und Koreanistik");
            this.put("DE-21-110", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Kriminologie");
            this.put("DE-21-112", "Universit\u00E4t T\u00FCbingen, Fakult\u00E4t f\u00FCr Biologie, Bibliothek");
            this.put("DE-21-116", "Universit\u00E4t T\u00FCbingen, Zentrum f\u00FCr Molekularbiologie der Pflanzen, Forschungsgruppe Pflanzenbiochemie");
            this.put("DE-21-117", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Medizinische Informationsverarbeitung");
            this.put("DE-21-118", "Universit\u00E4t T\u00FCbingen, Universit\u00E4ts-Archiv");
            this.put("DE-21-119", "Universit\u00E4t T\u00FCbingen, Wilhelm-Schickard-Institut f\u00FCr Informatik");
            this.put("DE-21-120", "Universit\u00E4t T\u00FCbingen, Asien-Orient-Institut, Abteilung f\u00FCr Japanologie");
            this.put("DE-21-121", "Universit\u00E4t T\u00FCbingen, Internationales Zentrum f\u00FCr Ethik in den Wissenschaften");
            this.put("DE-21-123", "Universit\u00E4t T\u00FCbingen, Medizinbibliothek");
            this.put("DE-21-124", "Universit\u00E4t T\u00FCbingen, Institut f. Medizinische Virologie und Epidemiologie d. Viruskrankheiten");
            this.put("DE-21-126", "Universit\u00E4t T\u00FCbingen, Institut f\u00FCr Medizinische Mikrobiologie und Hygiene");
            this.put("DE-21-203", "Universit\u00E4t T\u00FCbingen, Sammlung Werner Schweikert - Archiv der Weltliteratur");
            this.put("DE-21-205", "Universit\u00E4t T\u00FCbingen, Zentrum f\u00FCr Islamische Theologie");
            this.put("DE-Frei85", "Freiburg MPI Ausl\u00E4nd.Recht, Max-Planck-Institut f\u00FCr ausl\u00E4ndisches und internationales Strafrecht");
        }
    };
    private final static Pattern PAGE_RANGE_PATTERN1 = Pattern.compile("\\s*(\\d+)\\s*-\\s*(\\d+)$");
    private final static Pattern PAGE_RANGE_PATTERN2 = Pattern.compile("\\s*\\[(\\d+)\\]\\s*-\\s*(\\d+)$");
    private final static Pattern PAGE_RANGE_PATTERN3 = Pattern.compile("\\s*(\\d+)\\s*ff");
    private final static Pattern YEAR_PATTERN = Pattern.compile("(\\d\\d\\d\\d)");
    private final static Pattern VOLUME_PATTERN = Pattern.compile("^\\s*(\\d+)$");
    // Map used by getPhysicalType().
    private static final Map<String, String> phys_code_to_full_name_map;

    static {
        Map<String, String> tempMap = new HashMap<>();
        tempMap.put("arbtrans", "Transparency");
        tempMap.put("blindendr", "Braille");
        tempMap.put("bray", "Blu-ray Disc");
        tempMap.put("cdda", "CD");
        tempMap.put("ckop", "Microfiche");
        tempMap.put("cofz", "Online Resource");
        tempMap.put("crom", "CD-ROM");
        tempMap.put("dias", "Slides");
        tempMap.put("disk", "Diskette");
        tempMap.put("druck", "Printed Material");
        tempMap.put("dvda", "Audio DVD");
        tempMap.put("dvdr", "DVD-ROM");
        tempMap.put("dvdv", "Video DVD");
        tempMap.put("gegenst", "Physical Object");
        tempMap.put("handschr", "Longhand Text");
        tempMap.put("kunstbl", "Artistic Works on Paper");
        tempMap.put("lkop", "Mircofilm");
        tempMap.put("medi", "Multiple Media Types");
        tempMap.put("scha", "Record");
        tempMap.put("skop", "Microform");
        tempMap.put("sobildtt", "Audiovisual Carriers");
        tempMap.put("soerd", "Carriers of Other Electronic Data");
        tempMap.put("sott", "Carriers of Other Audiodata");
        tempMap.put("tonbd", "Audiotape");
        tempMap.put("tonks", "Audiocasette");
        tempMap.put("vika", "Videocasette");
        phys_code_to_full_name_map = Collections.unmodifiableMap(tempMap);
    }

    private Set<String> isils_cache = null;
    private Set<String> reviews_cache = null;
    private Set<String> reviewedRecords_cache = null;

    @Override
    public void perRecordInit() {
        reviews_cache = reviewedRecords_cache = isils_cache = null;
    }

    /**
     * Determine Record Title
     *
     * @param record the record
     * @return String     nicely formatted title
     */
    public String getTitle(final Record record) {
        final DataField title = (DataField) record.getVariableField("245");
        if (title == null)
            return null;

        final String title_a = (title.getSubfield('a') == null) ? null : title.getSubfield('a').getData();
        final String title_b = (title.getSubfield('b') == null) ? null : title.getSubfield('b').getData();
        if (title_a == null && title_b == null)
            return null;

        final StringBuilder complete_title = new StringBuilder();
        if (title_a == null)
            complete_title.append(Utils.cleanData(title_b));
        else if (title_b == null)
            complete_title.append(Utils.cleanData(title_a));
        else { // Neither title_a nor title_b are null.
            complete_title.append(Utils.cleanData(title_a));
            complete_title.append(" : ");
            complete_title.append(Utils.cleanData(title_b));
        }

        final String title_n = (title.getSubfield('n') == null) ? null : title.getSubfield('n').getData();
        if (title_n != null) {
            complete_title.append(' ');
            complete_title.append(Utils.cleanData(title_n));
        }

        return complete_title.toString();
    }

    /**
     * Determine Record Title Subfield
     *
     * @param record        the record
     * @param subfield_code
     * @return String     nicely formatted title subfield
     */
    public String getTitleSubfield(final Record record, final String subfield_code) {
        final DataField title = (DataField) record.getVariableField("245");
        if (title == null)
            return null;

        final Subfield subfield = title.getSubfield(subfield_code.charAt(0));
        if (subfield == null)
            return null;

        final String subfield_data = subfield.getData();
        if (subfield_data == null)
            return null;

        return Utils.cleanData(subfield_data);
    }

    /**
     * get the local subjects from LOK-tagged fields and get subjects from 936k and 689a subfields
     * <p/>
     * LOK = Field
     * |0 689 = Subfield
     * |a Imperialismus = Subfield with local subject
     *
     * @param record the record
     * @return Set of local subjects
     */
    public Set<String> getAllTopics(final Record record) {
        final Set<String> topics = SolrIndexerShim.instance().getAllSubfields(record, "600:610:611:630:650:653:656:689a:936a", " ");
        for (final VariableField variableField : record.getVariableFields("LOK")) {
            final DataField lokfield = (DataField) variableField;
            final Subfield subfield0 = lokfield.getSubfield('0');
            if (subfield0 == null || !subfield0.getData().equals("689  ")) {
                continue;
            }
            final Subfield subfieldA = lokfield.getSubfield('a');
            if (subfieldA == null || subfieldA.getData().length() <= 1) {
                continue;
            }
            topics.add(subfieldA.getData());
        }
        return topics;
    }

    /**
     * Hole das Sachschlagwort aus 689|a (wenn 689|d != z oder f)
     *
     * @param record the record
     * @return Set    "topic_facet"
     */
    public Set<String> getFacetTopics(final Record record) {
        final Set<String> result = SolrIndexerShim.instance().getAllSubfields(record, "600x:610x:611x:630x:648x:650a:650x:651x:655x", " ");
        String topic_string;
        // Check 689 subfield a and d
        final List<VariableField> fields = record.getVariableFields("689");
        if (fields != null) {
            DataField dataField;
            for (final VariableField variableField : fields) {
                dataField = (DataField) variableField;
                final Subfield subfieldD = dataField.getSubfield('d');
                if (subfieldD == null) {
                    continue;
                }
                topic_string = subfieldD.getData().toLowerCase();
                if (topic_string.equals("f") || topic_string.equals("z")) {
                    continue;
                }
                final Subfield subfieldA = dataField.getSubfield('a');
                if (subfieldA != null) {
                    result.add(subfieldA.getData());
                }
            }
        }
        return result;
    }

    /**
     * Finds the first subfield which is nonempty.
     *
     * @param dataField   the data field
     * @param subfieldIDs the subfield identifiers to search for
     * @return a nonempty subfield or null
     */
    private Subfield getFirstNonEmptySubfield(final DataField dataField, final char... subfieldIDs) {
        for (final char subfieldID : subfieldIDs) {
            for (final Subfield subfield : dataField.getSubfields(subfieldID)) {
                if (subfield != null && subfield.getData() != null && !subfield.getData().isEmpty()) {
                    return subfield;
                }
            }
        }
        return null;
    }

    public Set<String> getUrlsAndMaterialTypes(final Record record) {
        final Set<String> nonUnknownMaterialTypeURLs = new HashSet<String>();
        final Map<String, Set<String>> materialTypeToURLsMap = new TreeMap<String, Set<String>>();
        final Set<String> urls_and_material_types = new LinkedHashSet<>();
        for (final VariableField variableField : record.getVariableFields("856")) {
            final DataField field = (DataField) variableField;
            final Subfield materialTypeSubfield = getFirstNonEmptySubfield(field, '3', 'z', 'y', 'x');
            final String materialType = (materialTypeSubfield == null) ? UNKNOWN_MATERIAL_TYPE : materialTypeSubfield.getData();

            // Extract all links from u-subfields and resolve URNs:
            for (final Subfield subfield_u : field.getSubfields('u')) {
                Set<String> URLs = materialTypeToURLsMap.get(materialType);
                if (URLs == null) {
                    URLs = new HashSet<String>();
                    materialTypeToURLsMap.put(materialType, URLs);
                }

                final String rawLink = subfield_u.getData();
                final String link;
                if (rawLink.startsWith("urn:"))
                    link = "https://nbn-resolving.org/" + rawLink;
                else if (rawLink.startsWith("http://nbn-resolving.de"))
                    link = "https://nbn-resolving.org/" + rawLink.substring(23); // Replace HTTP w/ HTTPS.
                else if (rawLink.startsWith("http://nbn-resolving.org"))
                    link = "https://nbn-resolving.org/" + rawLink.substring(24); // Replace HTTP w/ HTTPS.
                else
                    link = rawLink;
                URLs.add(link);
                if (!materialType.equals(UNKNOWN_MATERIAL_TYPE)) {
                    nonUnknownMaterialTypeURLs.add(link);
                }
            }
        }

        // Remove duplicates while favouring SWB and, if not present, DNB links:
        for (final String material_type : materialTypeToURLsMap.keySet()) {
            if (material_type.equals(UNKNOWN_MATERIAL_TYPE)) {
                for (final String url : materialTypeToURLsMap.get(material_type)) {
                    if (!nonUnknownMaterialTypeURLs.contains(url)) {
                        urls_and_material_types.add(url + ":" + UNKNOWN_MATERIAL_TYPE);
                    }
                }
            } else {
                // Locate SWB and DNB URLs, if present:
                String preferredURL = null;
                for (final String url : materialTypeToURLsMap.get(material_type)) {
                    if (url.startsWith("http://swbplus.bsz-bw.de")) {
                        preferredURL = url;
                        break;
                    } else if (url.startsWith("http://d-nb.info"))
                        preferredURL = url;
                }

                if (preferredURL != null)
                    urls_and_material_types.add(preferredURL + ":" + material_type);
                else { // Add the kitchen sink.
                    for (final String url : materialTypeToURLsMap.get(material_type))
                        urls_and_material_types.add(url + ":" + material_type);
                }
            }
        }

        // Handle DOI's:
        for (final VariableField variableField : record.getVariableFields("024")) {
            final DataField field = (DataField) variableField;
            final Subfield subfield_2 = field.getSubfield('2');
            if (subfield_2 != null && subfield_2.getData().equals("doi")) {
                final Subfield subfield_a = field.getSubfield('a');
                if (subfield_a != null) {
                    final String url = "https://doi.org/" + subfield_a.getData();
                    urls_and_material_types.add(url + ":DOI");
                }
            }
        }

        return urls_and_material_types;
    }

    /**
     * Returns either a Set<String> of parent (ID + colon + parent title).  Only IDs w/o titles will not be returned,
     * instead a warning will be emitted on stderr.
     *
     * @param record the record
     * @return A, possibly empty, Set<String> containing the ID/title pairs.
     */
    public Set<String> getContainerIdsWithTitles(final Record record) {
        final Set<String> containerIdsAndTitles = new TreeSet<>();

        for (final String tag : new String[]{"800", "810", "830", "773"}) {
            for (final VariableField variableField : record.getVariableFields(tag)) {
                final DataField field = (DataField) variableField;
                final Subfield titleSubfield = getFirstNonEmptySubfield(field, 't', 'a');
                final Subfield volumeSubfield = field.getSubfield('v');
                final Subfield idSubfield = field.getSubfield('w');

                if (titleSubfield == null || idSubfield == null)
                    continue;

                final Matcher matcher = EXTRACTION_PATTERN.matcher(idSubfield.getData());
                if (!matcher.matches())
                    continue;
                final String parentId = matcher.group(1);

                containerIdsAndTitles.add(parentId + (char) 0x1F + titleSubfield.getData() + (char) 0x1F
                        + (volumeSubfield == null ? "" : volumeSubfield.getData()));
            }
        }
        return containerIdsAndTitles;
    }

    private void collectReviewsAndReviewedRecords(final Record record) {
        if (reviews_cache != null && reviewedRecords_cache != null) {
            return;
        }

        reviews_cache = new TreeSet<>();
        reviewedRecords_cache = new TreeSet<>();
        for (final VariableField variableField : record.getVariableFields("787")) {
            final DataField field = (DataField) variableField;
            final Subfield reviewTypeSubfield = getFirstNonEmptySubfield(field, 'i');
            final Subfield reviewerSubfield = getFirstNonEmptySubfield(field, 'a');
            final Subfield titleSubfield = getFirstNonEmptySubfield(field, 't');
            final Subfield idSubfield = field.getSubfield('w');

            if (reviewerSubfield == null || titleSubfield == null || idSubfield == null || reviewTypeSubfield == null)
                continue;

            final Matcher matcher = EXTRACTION_PATTERN.matcher(idSubfield.getData());
            if (!matcher.matches())
                continue;
            final String parentId = matcher.group(1);

            if (reviewTypeSubfield.getData().equals("Rezension")) {
                reviews_cache.add(parentId + (char) 0x1F + reviewerSubfield.getData() + (char) 0x1F + titleSubfield.getData());
            } else if (reviewTypeSubfield.getData().equals("Rezension von")) {
                reviewedRecords_cache.add(parentId + (char) 0x1F + reviewerSubfield.getData() + (char) 0x1F + titleSubfield.getData());
            }
        }
    }

    public Set<String> getReviews(final Record record) {
        collectReviewsAndReviewedRecords(record);
        return reviews_cache;
    }

    public Set<String> getReviewedRecords(final Record record) {
        collectReviewsAndReviewedRecords(record);
        return reviewedRecords_cache;
    }

    /**
     * @param record    the record
     * @param fieldnums
     * @return
     */
    public Set<String> getSuperMP(final Record record, final String fieldnums) {
        final Set<String> retval = new LinkedHashSet<>();
        final HashMap<String, String> resvalues = new HashMap<>();
        final HashMap<String, Integer> resscores = new HashMap<>();

        String value;
        String id;
        Integer score;
        Integer cscore;
        String fnum;
        String fsfc;

        final String[] fields = fieldnums.split(":");
        for (final String field : fields) {

            fnum = field.replaceAll("[a-z]+$", "");
            fsfc = field.replaceAll("^[0-9]+", "");

            final List<VariableField> fs = record.getVariableFields(fnum);
            if (fs == null) {
                continue;
            }
            for (final VariableField variableField : fs) {
                final DataField dataField = (DataField) variableField;
                final Subfield subfieldW = dataField.getSubfield('w');
                if (subfieldW == null) {
                    continue;
                }
                final Subfield fsubany = dataField.getSubfield(fsfc.charAt(0));
                if (fsubany == null) {
                    continue;
                }
                value = fsubany.getData().trim();
                id = subfieldW.getData().replaceAll("^\\([^\\)]+\\)", "");

                // Count number of commas in "value":
                score = value.length() - value.replace(",", "").length();

                if (resvalues.containsKey(id)) {
                    cscore = resscores.get(id);
                    if (cscore > score) {
                        continue;
                    }
                }
                resvalues.put(id, value);
                resscores.put(id, score);
            }
        }

        for (final String key : resvalues.keySet()) {
            value = "(" + key + ")" + resvalues.get(key);
            retval.add(value);
        }

        return retval;
    }

    /**
     * get the ISILs from LOK-tagged fields
     * <p/>
     * Typical LOK-Section below a Marc21 - Title-Set of a record:
     * LOK             |0 000 xxxxxnu a22 zn 4500
     * LOK             |0 001 000001376
     * LOK             |0 003 DE-576
     * LOK             |0 004 000000140
     * LOK             |0 005 20020725000000
     * LOK             |0 008 020725||||||||||||||||ger|||||||
     * LOK             |0 014   |a 000001368  |b DE-576
     * LOK             |0 541   |e 76.6176
     * LOK             |0 852   |a DE-Sp3
     * LOK             |0 852 1  |c B IV 529  |9 00
     * <p/>
     * LOK = Field
     * |0 852 = Subfield
     * |a DE-Sp3 = Subfield with ISIL
     *
     * @param record the record
     * @return Set of   isils
     */
    public Set<String> getIsils(final Record record) {
        if (isils_cache != null) {
            return isils_cache;
        }

        final Set<String> isils = new LinkedHashSet<>();
        final List<VariableField> fields = record.getVariableFields("LOK");
        if (fields != null) {
            for (final VariableField variableField : fields) {
                final DataField lokfield = (DataField) variableField;
                final Subfield subfield0 = lokfield.getSubfield('0');
                if (subfield0 == null || !subfield0.getData().startsWith("852")) {
                    continue;
                }
                final Subfield subfieldA = lokfield.getSubfield('a');
                if (subfieldA != null) {
                    isils.add(subfieldA.getData());
                }
            }
        }

        if (isils.isEmpty()) { // Nothing worked!
            isils.add("Unknown");
        }
        this.isils_cache = isils;
        return isils;
    }

    /**
     * @param record the record
     * @return
     */
    public String isAvailableInTuebingen(final Record record) {
        return Boolean.toString(!record.getVariableFields("SIG").isEmpty());
    }

    /**
     * get the collections from LOK-tagged fields
     * <p/>
     * Typical LOK-Section below a Marc21 - Title-Set of a record:
     * LOK             |0 000 xxxxxnu a22 zn 4500
     * LOK             |0 001 000001376
     * LOK             |0 003 DE-576
     * LOK             |0 004 000000140
     * LOK             |0 005 20020725000000
     * LOK             |0 008 020725||||||||||||||||ger|||||||
     * LOK             |0 014   |a 000001368  |b DE-576
     * LOK             |0 541   |e 76.6176
     * LOK             |0 852   |a DE-Sp3
     * LOK             |0 852 1  |c B IV 529  |9 00
     * <p/>
     * LOK = Field
     * |0 852 = Subfield
     * |a DE-Sp3 = Subfield with ISIL
     *
     * @param record the record
     * @return Set of  collections
     */
    public Set<String> getCollections(final Record record) {
        final Set<String> isils = getIsils(record);
        final Set<String> collections = new HashSet<>();
        for (final String isil : isils) {
            final String collection = isil_to_department_map.get(isil);
            if (collection != null) {
                collections.add(collection);
            } else {
                throw new IllegalArgumentException("Unknown ISIL: " + isil);
            }
        }

        if (collections.isEmpty())
            collections.add("Unknown");

        return collections;
    }

    /**
     * @param record the record
     */
    public String getInstitution(final Record record) {
        final Set<String> collections = getCollections(record);
        return collections.iterator().next();
    }

    /**
     * @param record the record
     */
    public String getBSZIndexedDate(final Record record) {
        for (final VariableField variableField : record.getVariableFields("LOK")) {
            final DataField lokfield = (DataField) variableField;
            final List<Subfield> subfields = lokfield.getSubfields();
            final Iterator<Subfield> subfieldsIter = subfields.iterator();
            while (subfieldsIter.hasNext()) {
                Subfield subfield = subfieldsIter.next();
                char formatCode = subfield.getCode();

                String dataString = subfield.getData();
                if (formatCode != '0' || !dataString.startsWith("938") || !subfieldsIter.hasNext()) {
                    continue;
                }

                subfield = subfieldsIter.next();
                formatCode = subfield.getCode();
                if (formatCode != 'a') {
                    continue;
                }

                dataString = subfield.getData();
                if (dataString.length() != 4) {
                    continue;
                }

                final String sub_year_text = dataString.substring(0, 2);
                final int sub_year = Integer.parseInt("20" + sub_year_text);
                final int current_year = Calendar.getInstance().get(Calendar.YEAR);
                final String year;
                if (sub_year > current_year) {
                    // It is from the last century
                    year = "19" + sub_year_text;
                } else {
                    year = "20" + sub_year_text;
                }

                final String month = dataString.substring(2, 4);
                return year + "-" + month + "-01T11:00:00:000Z";
            }
        }
        return null;
    }

    /**
     * @param record the record
     */
    public String getPageRange(final Record record) {
        final String field_value = SolrIndexerShim.instance().getFirstFieldVal(record, "936h");
        if (field_value == null)
            return null;

        final Matcher matcher1 = PAGE_RANGE_PATTERN1.matcher(field_value);
        if (matcher1.matches())
            return matcher1.group(1) + "-" + matcher1.group(2);

        final Matcher matcher2 = PAGE_RANGE_PATTERN2.matcher(field_value);
        if (matcher2.matches())
            return matcher2.group(1) + "-" + matcher2.group(2);

        final Matcher matcher3 = PAGE_RANGE_PATTERN3.matcher(field_value);
        if (matcher3.matches())
            return matcher3.group(1) + "-";

        return null;
    }

    /**
     * @param record the record
     */
    public String getContainerYear(final Record record) {
        final String field_value = SolrIndexerShim.instance().getFirstFieldVal(record, "936j");
        if (field_value == null)
            return null;

        final Matcher matcher = YEAR_PATTERN.matcher(field_value);
        return matcher.matches() ? matcher.group(1) : null;
    }

    /**
     * @param record the record
     */
    public String getContainerVolume(final Record record) {
        final String field_value = SolrIndexerShim.instance().getFirstFieldVal(record, "936d");
        if (field_value == null)
            return null;

        final Matcher matcher = VOLUME_PATTERN.matcher(field_value);
        return matcher.matches() ? matcher.group(1) : null;
    }

    /**
     * @param record the record
     */
    public Set<String> getPhysicalType(final Record record) {
        final Set<String> results = new TreeSet<>();
        for (final DataField data_field : record.getDataFields()) {
            if (!data_field.getTag().equals("935"))
                continue;

            final List<Subfield> physical_code_subfields = data_field.getSubfields('b');
            for (final Subfield physical_code_subfield : physical_code_subfields) {
                final String physical_code = physical_code_subfield.getData();
                if (phys_code_to_full_name_map.containsKey(physical_code))
                    results.add(phys_code_to_full_name_map.get(physical_code));
                else
                    System.err.println("in TuelibMixin.getPhysicalType: can't map \"" + physical_code + "\"!");
            }
        }

        return results;
    }

    /**
     * param record the record
     */
    public Set<String> getAuthor2AndRole(final Record record) {
        final Set<String> results = new TreeSet<>();
        for (final DataField data_field : record.getDataFields()) {
            if (!data_field.getTag().equals("700"))
                continue;
// Fixme: Query other author2 fields

            final String author2 = (data_field.getSubfield('a') != null) ?
                    data_field.getSubfield('a').getData() : "";
            final String author2role = (data_field.getSubfield('e') != null) ?
                    data_field.getSubfield('e').getData() : "";

            final StringBuilder author2AndRole = new StringBuilder();
            if (author2 != "" && author2role != "") {
                author2AndRole.append(author2);
                author2AndRole.append("$");
                author2AndRole.append(author2role);
                results.add(author2AndRole.toString());
            }
        }

        return results;
    }

    public Set<String> getValuesOrUnassigned(final Record record, final String fieldSpecs) {
        final Set<String> values = SolrIndexerShim.instance().getFieldList(record, fieldSpecs);
        if (values.isEmpty()) {
            values.add("[Unassigned]");
        }
        return values;
    }

    public String getFirstValueOrUnassigned(final Record record, final String fieldSpecs) {
        final Set<String> values = SolrIndexerShim.instance().getFieldList(record, fieldSpecs);
        if (values.isEmpty()) {
            values.add("[Unassigned]");
        }
        return values.iterator().next();
    }

    /**
     * Get all available dates from the record.
     *
     * @param record MARC record
     * @return set of dates
     */
    public Set<String> getDates(final Record record) {
        final Set<String> dates = new LinkedHashSet<>();

        // Check old-style 260c date:
        final List<VariableField> list534 = record.getVariableFields("534");
        for (final VariableField vf : list534) {
            final DataField df = (DataField) vf;
            final List<Subfield> currentDates = df.getSubfields('c');
            for (final Subfield sf : currentDates) {
                final String currentDateStr = Utils.cleanDate(sf.getData());
                dates.add(currentDateStr);
            }
        }
        if (!dates.isEmpty()) {
            return dates;
        }

        // Check old-style 260c date:
        final List<VariableField> list260 = record.getVariableFields("260");
        for (final VariableField vf : list260) {
            final DataField df = (DataField) vf;
            final List<Subfield> currentDates = df.getSubfields('c');
            for (final Subfield sf : currentDates) {
                final String currentDateStr = Utils.cleanDate(sf.getData());
                dates.add(currentDateStr);
            }
        }

        // Now track down relevant RDA-style 264c dates; we only care about
        // copyright and publication dates (and ignore copyright dates if
        // publication dates are present).
        final Set<String> pubDates = new LinkedHashSet<>();
        final Set<String> copyDates = new LinkedHashSet<>();
        final List<VariableField> list264 = record.getVariableFields("264");
        for (final VariableField vf : list264) {
            final DataField df = (DataField) vf;
            final List<Subfield> currentDates = df.getSubfields('c');
            for (final Subfield sf : currentDates) {
                final String currentDateStr = Utils.cleanDate(sf.getData());
                final char ind2 = df.getIndicator2();
                switch (ind2) {
                    case '1':
                        pubDates.add(currentDateStr);
                        break;
                    case '4':
                        copyDates.add(currentDateStr);
                        break;
                }
            }
        }
        if (!pubDates.isEmpty()) {
            dates.addAll(pubDates);
        } else if (!copyDates.isEmpty()) {
            dates.addAll(copyDates);
        }

        return dates;
    }

    /**
     * Get the earliest publication date from the record.
     *
     * Fix for NullPointerException!
     *
     * @param record MARC record
     * @return earliest date
     */
    public String getFirstDate(final Record record) {
        String result = null;
        final Set<String> dates = getDates(record);
        for (final String current : dates) {
            if (result == null || current != null && Integer.parseInt(current) < Integer.parseInt(result)) {
                result = current;
            }
        }
        return result;
    }

    public String isSuperiorWork(final Record record) {
        return Boolean.toString(record.getVariableField("SPR") != null);
    }
}
