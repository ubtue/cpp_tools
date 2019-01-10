#!/bin/bash
if [[ $# > 1 ]]; then
    echo "usage: $0 [system_type]"
    echo "          tuefind: Also install tuefind dependencies"
    exit 1
fi

function ColorEcho {
    echo -e "\033[1;34m" $1 "\033[0m"
}

if [[ $1 != "" && $1 != "tuefind" ]]; then
    ColorEcho "invalid system_type \"$1\"!"
    exit 1
fi

#--------------------------------- UB_TOOLS ---------------------------------#
ColorEcho "installing/updating ub_tools dependencies..."

apt-get --yes update

# install software-properties-common for apt-add-repository
apt-get --yes install software-properties-common

# main installation
apt-get --quiet --yes --allow-unauthenticated install \
    curl wget \
    ant cifs-utils clang cron gcc git locales-all make openjdk-8-jdk sudo \
    apache2 ca-certificates libarchive-dev libcurl4-gnutls-dev libkyotocabinet-dev liblept5 libleptonica-dev liblz4-tool libmagic-dev libmysqlclient-dev libpcre3-dev libpoppler73 libsqlite3-dev libssl-dev libtesseract-dev libtokyocabinet-dev libwebp6 libxerces-c-dev libxml2-dev libxml2-utils mawk mysql-utilities poppler-utils unzip uuid-dev \
    tesseract-ocr tesseract-ocr-bul tesseract-ocr-ces tesseract-ocr-dan tesseract-ocr-deu tesseract-ocr-eng tesseract-ocr-fin tesseract-ocr-fra tesseract-ocr-heb tesseract-ocr-hun tesseract-ocr-ita tesseract-ocr-lat tesseract-ocr-nld tesseract-ocr-nor tesseract-ocr-pol tesseract-ocr-por tesseract-ocr-rus tesseract-ocr-script-grek tesseract-ocr-slv tesseract-ocr-spa tesseract-ocr-swe

# From 18.04 on, Java 8 needs to be enabled as well for Solr + mixins (18.04 ships with 10)
# (unfortunately, >= string comparison is impossible in Bash, so we compare > 17.10)
. /etc/lsb-release
if [[ $DISTRIB_RELEASE > "17.10" ]]; then
    update-alternatives --set java /usr/lib/jvm/java-8-openjdk-amd64/jre/bin/java
fi

#mysql installation
## (use "quiet" and set frontend to noninteractive so mysql doesnt ask for a root password, geographic area and timezone)
DEBIAN_FRONTEND_OLD=($DEBIAN_FRONTEND)
export DEBIAN_FRONTEND="noninteractive"
apt-get --quiet --yes --allow-unauthenticated install mysql-server
export DEBIAN_FRONTEND=(DEBIAN_FRONTEND_OLD)
## create /var/run/mysqld and change user (mysql installation right now has a bug not doing that itself)
## (chown needs to be done after installation = after the user has been created)
mkdir -p /var/run/mysqld
chown -R mysql:mysql /var/run/mysqld

#---------------------------------- TUEFIND ---------------------------------#
if [[ $1 == "tuefind" ]]; then
    ColorEcho "installing/updating tuefind dependencies..."

    apt-get --quiet --yes install \
        composer \
        php php-curl php-gd php-intl php-json php-ldap php-mbstring php-mysql php-soap php-xsl php-pear \
        libapache2-mod-php

    a2enmod rewrite
    a2enmod ssl
    /etc/init.d/apache2 restart
fi

ColorEcho "finished installing/updating dependencies"
