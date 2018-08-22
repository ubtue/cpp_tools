#!/bin/bash
set -o errexit -o nounset


no_problems_found=1
function SendEmail {
    if [[ $no_problems_found -eq 0 ]]; then
        send_email --recipients="$email_address" --subject="$0 passed on $(hostname)" --message-body="No problems were encountered."
        exit 0
    else
        send_email --priority=high --recipients="$email_address" --subject="$0 failed on $(hostname)" \
                   --message-body="Check /usr/local/var/log/tuefind/merge_differential_and_full_marc_updates.log for details."
        exit 1
    fi
}
trap SendEmail EXIT


function Usage() {
    echo "Usage: $0 [--keep-intermediate-files] email_address"
    exit 1
}


# Argument processing
KEEP_ITERMEDIATE_FILES=
if [[ $# > 1 ]]; then
    if [[ $1 == "--keep-intermediate-files" ]]; then
        KEEP_ITERMEDIATE_FILES="--keep-intermediate-files"
    else
        Usage
    fi
    shift
fi
if [[ $# != 1 ]]; then
    Usage
fi
email_address=$1


target_filename=Complete-MARC-$(date +%y%m%d).tar.gz
if [[ -e $target_filename ]]; then
    echo "Nothing to do: ${target_filename} already exists."
    exit 0
fi
echo "Creating ${target_filename}"


input_filename=$(generate_merge_order | head --lines=1)

# Create a subdirectory from the input archive:
extraction_directory="${input_filename%.tar.gz}"
mkdir "$extraction_directory"
cd "$extraction_directory"
tar xzf ../"$input_filename"
cd -

input_directory=$extraction_directory

declare -i counter=0
last_temp_directory=
for update in $(generate_merge_order | tail --lines=+2); do
    ((++counter))
    temp_directory=temp_directory.$BASHPID.$counter
    if [[ ${update:0:6} == "LOEPPN" ]]; then
        echo "Processing deletion list: $update"
        echo archive_delete_ids $KEEP_ITERMEDIATE_FILES $input_directory $update $temp_directory
        archive_delete_ids $KEEP_ITERMEDIATE_FILES $input_directory $update $temp_directory
    else
        echo "Processing differential dump: $update"
        echo apply_differential_update $KEEP_ITERMEDIATE_FILES $input_directory $update $temp_directory
        apply_differential_update $KEEP_ITERMEDIATE_FILES $input_directory $update $temp_directory
    fi
    if [[ -n "$last_temp_directory" ]]; then
        rm -r ${last_temp_directory}
    fi
    input_directory=$temp_directory
    last_temp_directory=$temp_directory
done


# If we did not execute the for-loop at all, $temp_directory is unset and we need to set it to the empty string:
temp_directory=${temp_directory:-}

if [ -z ${temp_directory} ]; then
    ln --symbolic --force $input_filename Complete-MARC-current.tar.gz
else
    rm -r "$extraction_directory"
    cd ${temp_directory}
    tar czf ../$target_filename *mrc
    cd ..
    rm -r ${temp_directory}

    if [[ ! keep_itermediate_filenames ]]; then
        rm temp_directory.$BASHPID.* TA-*.tar.gz WA-*.tar.gz SA-*.tar.gz
    fi

    # Create symlink to newest complete dump:
    ln --symbolic --force $target_filename Complete-MARC-current.tar.gz
fi


no_problems_found=0
