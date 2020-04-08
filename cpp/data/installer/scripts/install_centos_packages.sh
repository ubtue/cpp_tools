#!/bin/bash
if [[ $# > 1 ]]; then
    echo "usage: $0 [system_type]"
    echo "          ixtheo|krimdok: Also install specific dependencies"
    exit 1
fi

function ColorEcho {
    echo -e "\033[1;34m" $1 "\033[0m"
}

function InstallIfMissing {
    if dnf list installed $1 | grep --quiet $1; then
        ColorEcho "\"$1\" already installed"
    else
        dnf --assumeyes install $1
    fi
}

if [[ $1 != "" && $1 != "ixtheo" && $1 != "krimdok" ]]; then
    ColorEcho "invalid system_type \"$1\"!"
    exit 1
fi

#--------------------------------- UB_TOOLS ---------------------------------#
ColorEcho "installing/updating ub_tools dependencies..."

# make sure dnf config-manager plugin is installed (Docker)
dnf --assumeyes install dnf-plugins-core

# epel-release needs to be installed first, else several packages won't be found
dnf --assumeyes install curl epel-release wget

# additional repos (Alexander_Pozdnyakov = tesseract)
dnf config-manager --set-enabled PowerTools
dnf config-manager --add-repo https://raw.githubusercontent.com/ubtue/ub_tools/master/cpp/data/installer/elasticsearch.repo
dnf config-manager --add-repo https://download.opensuse.org/repositories/home:/Alexander_Pozdnyakov/CentOS_8/
rpm --import https://build.opensuse.org/projects/home:Alexander_Pozdnyakov/public_key
dnf --assumeyes update

# basic dependencies
InstallIfMissing "ca-certificates"
dnf --assumeyes install \
    ant bc cifs-utils clang crontabs ftp gcc-c++ glibc-all-langpacks git java-1.8.0-openjdk-devel make python3 sudo \
    gawk ImageMagick jq libcurl-devel libdb-devel libsq3-devel libuuid-devel libwebp libxml2-devel libxml2 lsof lz4 mariadb mariadb-devel mariadb-server mariadb-server-utils mod_ssl openssl-devel pcre-devel policycoreutils-python-utils poppler poppler-utils rpmdevtools unzip xerces-c-devel \
    libcurl-devel tidy

dnf --assumeyes --repo=download.opensuse.org_repositories_home_Alexander_Pozdnyakov_CentOS_8_ install \
    tesseract tesseract-devel tesseract-langpack-bul tesseract-langpack-ces tesseract-langpack-dan tesseract-langpack-deu tesseract-langpack-eng tesseract-langpack-fin tesseract-langpack-fra tesseract-langpack-grc tesseract-langpack-heb tesseract-langpack-hun tesseract-langpack-ita tesseract-langpack-lat tesseract-langpack-nld tesseract-langpack-nor tesseract-langpack-pol tesseract-langpack-por tesseract-langpack-rus tesseract-langpack-slv tesseract-langpack-spa tesseract-langpack-swe

# PowerTools dependencies
dnf --assumeyes install file-devel glibc-static leptonica-devel libarchive-devel openjpeg2-devel

# g++, clang++ etc.
dnf --assumeyes group install "Development Tools"
dnf --assumeyes install llvm-toolset

# Make Johannes happy :-)
dnf --assumeyes install tmux emacs

# Elasticsearch for fulltext
if [[ $1 == "krimdok" || $1 == "fulltext_backend" ]]; then
    ColorEcho "Installing Elasticsearch"
    InstallIfMissing elasticsearch
    if ! /usr/share/elasticsearch/bin/elasticsearch-plugin list | grep --quiet analysis-icu; then
        /usr/share/elasticsearch/bin/elasticsearch-plugin install analysis-icu
    fi
    mkdir --parents /etc/elasticsearch/synonyms
    for i in all de en fr it es pt ru el hans hant; do touch /etc/elasticsearch/synonyms/synonyms_$i.txt; done
fi


### TUEFIND ###
if [[ $1 == "ixtheo" || $1 == "krimdok" ]]; then
    ColorEcho "installing/updating tuefind dependencies..."

    # PHP
    dnf --assumeyes install php php-cli php-common php-gd php-intl php-json php-ldap php-mbstring php-mysqlnd php-soap php-xml

    # composer also needs to be installed manually to avoid php dependency problems
    if [ -e /usr/local/bin/composer ]; then
        ColorEcho "composer already installed"
    else
        ColorEcho "installing composer"
        wget --output-document=/tmp/composer-setup.php https://getcomposer.org/installer
        php /tmp/composer-setup.php --install-dir=/usr/local/bin --filename=composer
    fi
fi

ColorEcho "finished installing/updating dependencies"
