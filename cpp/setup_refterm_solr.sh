#!/bin/bash
set -o errexit -o nounset

FILE_TO_IMPORT="$1"
VUFIND_HOME=/usr/local/vufind
VUFIND_SOLRMARC_HOME=$VUFIND_HOME/import/
UB_TOOLS_HOME=/usr/local/ub_tools/
CONFIG_FILE_DIR=$UB_TOOLS_HOME/cpp/data/refterm_solr_conf
LOGDIR=/mnt/zram/log/ 


export SOLR_BIN="$VUFIND_HOME"/solr/vendor/bin/
export SOLRMARC_HOME=/mnt/zram/import
export SOLR_HOME=/mnt/zram/solr/vufind/
export SOLR_PORT=8081

trap ExitHandler SIGINT

Usage() {
    cat << EOF
Sets up a a temporary Solr instance in a Ramdisk and imports the MARC21 data given as a parameter

USAGE: "${0##*/}" FILE_TO_IMPORT
EOF
}


function ExitHandler {
   shutdown_ramdisk
}


# Call with a single error_msg argument.
ErrorExit() {
    >&2 echo "$0: $1"
    exit 1
}


SetupRamdisk() {
    # Nothing to do?
    test -e /mnt/zram && mountpoint --quiet /mnt/zram && return

    if ! modprobe zram num_devices=1; then
        ErrorExit 'Failed to load ZRAM module!'
    fi

    /usr/local/sbin/zramctl --reset /dev/zram0
    /usr/local/sbin/zramctl --size 2GiB /dev/zram0

    # Create a file system in RAM...
    if ! mkfs.ext4 -q -m 0 -b 4096 -O sparse_super -L zram /dev/zram0; then
        ErrorExit 'Failed to create an Ext4 file system in RAM!'
    fi
    # ...and mount it.
    if ! mount -o relatime,nosuid /dev/zram0 /mnt/zram; then
        ErrorExit 'Failed to mount our RAM disk!'
    fi
}


# Abort if we are not root or the parameters do not match
test "$EUID" -eq 0 || ErrorExit 'We can only run as root!'
if [[ $# != 1 ]]; then
    >&2 echo "$0: Invalid number of parameters"'!'
    Usage
    exit 1
fi

# Setup zram
SetupRamdisk
mkdir --parents "$LOGDIR"

# Copy the config directory to zram
rsync --archive --recursive "$CONFIG_FILE_DIR/" /mnt/zram
# Copy jars to zram
rsync --archive --include='*.jar' --exclude='*' "$VUFIND_SOLRMARC_HOME" /mnt/zram/import
rsync --archive "$VUFIND_SOLRMARC_HOME"/lib /mnt/zram/import
rsync --archive "$VUFIND_SOLRMARC_HOME"/bin /mnt/zram/import
rsync --archive "$VUFIND_SOLRMARC_HOME"/lib_local /mnt/zram/import
rsync --archive "$VUFIND_SOLRMARC_HOME"/index_java /mnt/zram/import

# Set up and start Solr
/mnt/zram/solr.sh start
if [ $? -ne 0 ]; then
    >&2 echo "$0"': Failed to start Solr!'
    exit 1
fi

# Import the MARC files
/mnt/zram/import-marc.sh -p /mnt/zram/import/import.properties "$FILE_TO_IMPORT" 2>&1 
if [ $? -ne 0 ]; then
    >&2 echo "$0"': Failed to import MARC files!'
    exit 1
fi
