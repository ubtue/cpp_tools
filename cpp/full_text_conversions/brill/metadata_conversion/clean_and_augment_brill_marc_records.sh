#!/bin/bash
set -o errexit -o nounset -o pipefail

trap RemoveTempFiles EXIT

if [ $# != 2 ]; then
    echo "usage: $0 brill_reference_input_marc.xml output.xml"
    exit 1
fi


function RemoveTempFiles {
    rm ${tmpfile1} ${tmpfile2}
}

TOOL_BASE_PATH="/usr/local/ub_tools/cpp/full_text_conversions/brill/metadata_conversion"
ADJUST_YEAR_XSLT="xsl/adjust_year.xsl"
input_file="$1"
output_file="$2"
tmpfile1=$(mktemp -t marc_clean1XXXXX.xml)
tmpfile2=$(mktemp -t marc_clean2XXXXX.xml)

EECO_superior=$(printf "%s" '773i:Enthalten in\037tBrill Encyclopedia of Early Christianity Online\037dLeiden : Brill, 2018' \
                            '\037g2018' \
                            '\037hOnline-Ressource' \
                            '\037w(DE-627)1042525064\037w(DE-600)2952192-0\037w(DE-576)514794658')

BDRO_superior=$(printf "%s" '773i:Enthalten in\037tThe Brill dictionary of religion\037dLeiden : Brill, 2006' \
                            '\037g2006' \
                            '\037hOnline-Ressource' \
                            '\037w(DE-627)1653634359\037w(DE-576)422642290')

BEHO_superior=$(printf "%s" '773i:Enthalten in\037tBrill'"'"'s Encyclopedia of Hinduism\037dLeiden : Brill, 2012' \
                            '\037g2012' \
                            '\037hOnline-Ressource' \
                            '\037w(DE-627)734740913\037w(DE-600)2698886-0\037w(DE-576)377732672')

BEJO_superior=$(printf "%s" '773i:Enthalten in\037tBrill'"'"'s Encyclopedia of Jainism Online\037dLeiden : Brill,2020' \
                            '\037g2020' \
                            '\037hOnline-Ressource' \
                            '\037w(DE-627)1693246007')



# Remove superfluous fields and fix deceased author information
marc_filter ${input_file} ${tmpfile1} \
    --remove-fields '500a:Converted from MODS 3.7 to MARCXML.*' \
    --remove-fields '540a:.*' --remove-fields '787t:' \
    --remove-fields '500a:^...\s*$' \
    --remove-fields '500a:^Author passed away: insert behind name  [(]†[)]...$' \
    --remove-fields '008:.*' \
    --replace '100a:700a' '(.*)\s*[(]†[)]\s*' '\1'

# Insert additionally needed fields
marc_augmentor ${tmpfile1} ${tmpfile2} \
    --insert-field-if "${EECO_superior}" '001:EECO.*' \
    --insert-field-if "${BDRO_superior}" '001:BDRO.*' \
    --insert-field-if "${BEHO_superior}" '001:BEHO.*' \
    --insert-field-if "${BEJO_superior}" '001:BEJO.*' \
    --insert-field '003:DE-Tue135' \
    --insert-field '005:'$(date +'%Y%m%d%H%M%S')'.0' \
    --insert-field '007:cr|||||' \
    --insert-field '084a:1\0372ssgn' \
    `# tag relbib appropriately` \
    --add-subfield-if '084a:0' '001:BEHO.*|BEJO.*' \
    --insert-field '338a:Online-Resource\037bcr\0372rdacarrier' \
    --insert-field '852a:DE-Tue135' \
    --insert-field '935c:uwlx' \
    --insert-field '935a:mteo' \
    --insert-field '936j:XXX' \
    --insert-field 'ELCa:1'

# Fix indicators and year information
cat ${tmpfile2} | \
    xmlstarlet ed -O -u '//_:datafield[@tag="773"]/@ind1' -v "0" \
       -u '//_:datafield[@tag="773"]/@ind2' -v "8" \
       -u '//_:datafield[@tag="936"]/@ind1' -v "u" \
       -u '//_:datafield[@tag="936"]/@ind2' -v "w" |
    xmlstarlet tr ${TOOL_BASE_PATH}/${ADJUST_YEAR_XSLT} \
       > ${output_file}