#!/bin/bash
if [[ $# > 1 ]]; then
    echo "usage: $0 [system_type]"
    echo "          tuefind: Also install PHP/Apache/MySQL + JDK"
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
# (use "quiet" so mysql hopefully doesnt ask for a root password, geographic area and timezone)
apt-get --quiet --yes --allow-unauthenticated install \
    curl wget \
    ant cifs-utils clang cron gcc git locales-all make sudo \
    ca-certificates libarchive-dev libboost-all-dev libcurl4-gnutls-dev libkyotocabinet-dev liblept5 libleptonica-dev liblz4-tool libmagic-dev libmysqlclient-dev libpcre3-dev libpoppler73 libsqlite3-dev libssl-dev libtesseract-dev libtokyocabinet-dev libwebp6 libxml2-dev libxml2-utils mawk poppler-utils uuid-dev \
    tesseract-ocr tesseract-ocr-bul tesseract-ocr-ces tesseract-ocr-dan tesseract-ocr-deu tesseract-ocr-eng tesseract-ocr-fin tesseract-ocr-fra tesseract-ocr-heb tesseract-ocr-hun tesseract-ocr-ita tesseract-ocr-lat tesseract-ocr-nld tesseract-ocr-nor tesseract-ocr-pol tesseract-ocr-por tesseract-ocr-rus tesseract-ocr-script-grek tesseract-ocr-slv tesseract-ocr-spa tesseract-ocr-swe

#---------------------------------- TUEFIND ---------------------------------#
if [[ $1 == "tuefind" ]]; then
    ColorEcho "installing/updating tuefind dependencies..."

    # set frontend to noninteractive (so mysql-server wont ask for root pw, timezone, and so on)
    DEBIAN_FRONTEND_OLD=($DEBIAN_FRONTEND)
    export DEBIAN_FRONTEND="noninteractive"

    apt-get --quiet --yes install \
        composer unzip openjdk-8-jdk \
        apache2 mysql-server \
        php php-curl php-gd php-intl php-json php-ldap php-mbstring php-mysql php-xsl php-pear \
        libapache2-mod-php

    # create /var/run/mysqld and change user (mysql installation right now has a bug not doing that itself)
    # (chown needs to be done after installation = after the user has been created)

    export DEBIAN_FRONTEND=(DEBIAN_FRONTEND_OLD)
    mkdir -p /var/run/mysqld
    chown -R mysql:mysql /var/run/mysqld

    a2enmod rewrite
    a2enmod ssl
    /etc/init.d/apache2 restart
fi

ColorEcho "finished installing/updating dependencies"
