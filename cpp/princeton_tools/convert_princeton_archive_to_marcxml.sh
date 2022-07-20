#!/bin/bash
set -o errexit -o nounset -o pipefail

if [ $# != 2 ]; then
    echo "usage: $0 ptsem-XX.zip output.mrc"
    exit 1
fi

archive_file="$1"
output_file="$2"
archive_contents=$(7z l ${archive_file} | grep 'xml$' | awk '{ print $6 }')
TOOL_BASE_PATH="/usr/local/ub_tools/cpp/princeton_tools"
XSLT_FILE="MODS3-7_MARC21slim_XSLT1-0_ubtue_princeton.xsl"
PPN_BASE=$(echo ${archive_file} | sed -r -e 's/ptsem-([[:digit:]]+)\.zip/\1/')
SKIP_LIST=('annbi00bibl.xml' 'thechildsbookons00unse.xml' 'earlyyearsofchri03pres.xml' 'thechoiceseerbyg00dyke.xml')

> ${output_file}
echo '<?xml version="1.0" encoding="UTF-8"?>' >> ${output_file}
echo '<collection>' >> ${output_file}
i=0
for content in ${archive_contents}; do
     i=$((i+1))
     ppn=$(printf "${PPN_BASE}_%06d" ${i})
     echo ${ppn}
     echo ${content}
     #c.f. https://stackoverflow.com/questions/3685970/check-if-a-bash-array-contains-a-value
     if [[ " ${SKIP_LIST[*]} " =~ " ${content} " ]]; then
         echo "Skipping ${content}"
         continue
     fi
     7z x -so ${archive_file} ${content} | \
         xmlstarlet ed -d '//_:subject[@authority="aat" or @authority="local" or @authority="rbgenr"]' | \
         xmlstarlet tr ${TOOL_BASE_PATH}/${XSLT_FILE} | \
         xmlstarlet ed -O -a //marc:leader -t elem -n 'marc:controlfield' -v "${ppn}"  \
                    --var new_node '$prev' -i '$new_node' -t attr -n "tag" -v "001" | \
         sed -r -e 's/(<[/]?)marc:/\1/g' | \
         sed -r -e 's/(<record).*>/\1>/g' >> ${output_file}
#     if [[ ${i} -gt 20 ]]; then
#         break
#     fi
done
echo '</collection>' >> ${output_file}
