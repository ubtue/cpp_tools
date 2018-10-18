#!/bin/bash
# Script for generating and uploading KrimDok-relevant SSOAR data to the BSZ FTP server.
set -e

echo "Download the data from SSOAR"
oai_pmh_harvester https://www.ssoar.info/OAIHandler/request marcxml col_collection_10214 KRIM_SSOAR krim_ssoar.xml 20


if [[ $(marc_size krim_ssoar.xml) == 0 ]]; then
    echo "No new data found."
    exit 0
fi


echo "Remove superfluous subfields"
filtered_file="krim_ssoar_filtered.xml"
marc_filter krim_ssoar.xml "$filtered_file" \
    --remove-subfields '7737:nnas'


filtered_file1="krim_ssoar_filtered1.xml"
marc_filter "$filtered_file" "$filtered_file1" \
    --remove-subfields '856s:^\s+bytes'


echo "Add various selection identifiers"
augmented_file="krim_ssoar_augmented.xml"
marc_augmentor "$filtered_file1" "$augmented_file" \
    --insert-field '084:  \x1FaKRIM\x1FqDE-21\x1F2fid' \
    --insert-field '852a:DE-2619' \
    --insert-field '935a:mkri' \
    --insert-field 'LOK:  \x1F0935\x1Fasoar'


echo "Rewrite some of the contents"
rewritten_file="krim_ssoar-$(date +%Y%m%d).xml"
rewrite_ssoar $augmented_file $rewritten_file

#echo "Uploading to the BSZ File Server"
#upload_to_bsz_ftp_server.sh "$rewritten_file" "/pub/UBTuebingen_Import_Test/krimdok_Test"

echo '*** DONE ***'
