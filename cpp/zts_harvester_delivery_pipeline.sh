#!/bin/bash
# Runs through the phases of the Zotero Harvester delivery pipeline.
set -o errexit -o nounset


no_problems_found=1
function SendEmail {
    if [[ $no_problems_found -eq 0 ]]; then
        send_email --recipients="$email_address" --subject="$0 passed on $(hostname)" --message-body="No problems were encountered."
        exit 0
    else
        send_email --priority=high --recipients="$email_address" --subject="$0 failed on $(hostname)" \
                   --message-body="Check /usr/local/var/log/tuefind/zts_harvester_delivery_pipeline.log for details."
        echo "*** ZTS_HARVESTER DELIVERY PIPELINE FAILED ***" | tee --append "${log}"
        exit 1
    fi
}
trap SendEmail EXIT


function Usage {
    echo "usage: $0 mode email"
    echo "       mode = TEST|LIVE"
    echo "       email = email address to which notifications are sent upon (un)successful completion of the delivery pipeline"
    exit 1
}


if [ $# != 2 ]; then
    Usage
fi


if [ "$1" != "TEST" ] && [ "$1" != "LIVE" ]; then
    echo "unknown mode '$1'"
    Usage
fi


delivery_mode=$1
email_address=$2
working_directory=/tmp/zts_harvester_delivery_pipeline

harvester_output_directory=$working_directory
harvester_output_filename=zts_harvester-$(date +%y%m%d).xml
harvester_config_file=/usr/local/ub_tools/cpp/data/zts_harvester.conf
missing_metadata_tracker_output_filename=zts_harvester-$(date +%y%m%d)-missing-metadata.log


function StartPhase {
    if [ -z ${PHASE+x} ]; then
        PHASE=1
    else
        ((++PHASE))
    fi
    START=$(date +%s.%N)
    echo "*** Phase $PHASE: $1 - $(date) ***" | tee --append "${log}"
}


# Call with "CalculateTimeDifference $start $end".
# $start and $end have to be in seconds.
# Returns the difference in fractional minutes as a string.
function CalculateTimeDifference {
    start=$1
    end=$2
    echo "scale=2;($end - $start)/60" | bc --mathlib
}


function EndPhase {
    PHASE_DURATION=$(CalculateTimeDifference $START $(date +%s.%N))
    echo -e "Done after ${PHASE_DURATION} minutes.\n" | tee --append "${log}"
}


function EndPipeline {
    echo -e "\n\nPipeline done after $(CalculateTimeDifference $OVERALL_START $(date +%s.%N)) minutes." | tee --append "${log}"
    echo "*** ZTS_HARVESTER DELIVERY PIPELINE DONE ***" | tee --append "${log}"
    no_problems_found=0
    exit 0
}


# Set up the log file:
logdir=/usr/local/var/log/tuefind
log_filename=$(basename "$0")
log="${logdir}/${log_filename%.*}.log"
rm -f "${log}"

# Cleanup files/folders from a previous run
mkdir -p $harvester_output_directory
rm -r -f -d $harvester_output_directory/*


OVERALL_START=$(date +%s.%N)
declare -a source_filepaths
declare -a dest_filepaths


StartPhase "Harvest URLs"
LOGGER_FORMAT=no_decorations,strip_call_site \
BACKTRACE=1 \
zts_harvester --min-log-level=INFO \
             --delivery-mode=$delivery_mode \
             --output-directory=$harvester_output_directory \
             --output-filename=$harvester_output_filename \
             $harvester_config_file >> "${log}" 2>&1
EndPhase


StartPhase "Collate File Paths"
cd $harvester_output_directory
counter=0
for d in */ ; do
    d=${d%/}
    if [[ $d -ef $harvester_output_directory ]]; then
        continue
    fi

    current_source_filepath=$harvester_output_directory/$d/$harvester_output_filename
    record_count=$(marc_size "$current_source_filepath")
    if [ "$record_count" = "0" ]; then
        continue    # skip files with zero records
    fi

    source_filepaths[$counter]=$current_source_filepath
    if [ "$delivery_mode" = "TEST" ]; then
        dest_filepaths[$counter]=/pub/UBTuebingen_Import_Test/"$d"_Test/
    elif [ "$delivery_mode" = "LIVE" ]; then
        dest_filepaths[$counter]=/pub/UBTuebingen_Import/$d/
    fi
    counter=$((counter+1))
done

if [ "$counter" = "0" ]; then
    echo -e "No new records were harvested"
    EndPipeline
fi
EndPhase


StartPhase "Validate Generated Records"
for source_filepath in "${source_filepaths[@]}"; do
    find_missing_metadata $source_filepath \
                          $working_directory/$missing_metadata_tracker_output_filename >> "${log}" 2>&1
done
EndPhase

StartPhase "Upload to BSZ Server"
counter=0
file_count=${#source_filepaths[@]}

while [ "$counter" -lt "$file_count" ]; do
    upload_to_bsz_ftp_server.sh ${source_filepaths[counter]} \
                                ${dest_filepaths[counter]} >> "${log}" 2>&1
    counter=$((counter+1))
done
EndPhase


StartPhase "Archive Sent Records"
for source_filepath in "${source_filepaths[@]}"; do
    archive_sent_records $source_filepath >> "${log}" 2>&1
done
EndPhase


# End the pipeline early for test deliveries
if [ "$delivery_mode" = "TEST"]; then
    EndPipeline
fi


StartPhase "Check for Overdue Articles"
journal_timeliness_checker "$harvester_config_file" "journal_timeliness_checker@$(hostname)" "$email_address"
EndPhase


EndPipeline
