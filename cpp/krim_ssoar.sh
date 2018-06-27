#!/bin/bash
# Script for generating and uploading KrimDok-relevant SSOAR data to the BSZ FTP server.
set -e

echo "Download the data from SSOAR"
oai_pmh_harvester --skip-dups https://www.ssoar.info/OAIHandler/request marcxml col_collection_10207 KRIM_SSOAR krim_ssoar.xml 20


if [[ $(marc_size krim_ssoar.xml) == 0 ]]; then
    echo "No new data found."
    exit 0
fi


echo "Add various selection identifiers"
augmented_file="krim_ssoar-$(date +%Y%m%d).xml"
marc_augmentor krim_ssoar.xml "$augmented_file" \
    --insert-field '084:  \x1FaKRIM\x1FqDE-21\x1F2fid' \
    --insert-field '852a:DE-21' \
    --insert-field '935a:mkri'


echo "Uploading to the BSZ File Server"
upload_to_bsz_ftp_server.sh "$augmented_file" "/pub/UBTuebingen_Import_Test/krimdok_Test"

echo '*** DONE ***'
