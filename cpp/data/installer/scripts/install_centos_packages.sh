#!/bin/bash
if [[ $# > 1 ]]; then
    echo "usage: $0 [system_type]"
    echo "          tuefind: Also install PHP/Apache/MySQL + JDK"
    exit 1
fi

function ColorEcho {
    echo -e "\033[1;34m" $1 "\033[0m"
}

#--------------------------------- UB_TOOLS ---------------------------------#
ColorEcho "installing/updating ub_tools dependencies..."

# epel-release needs to be installed first, else packages like kyotocabinet won't be found
yum --assumeyes install curl epel-release wget

# additional repos (shibboleth = libcurl-openssl-devel.x86_64)
cd /etc/yum.repos.d/
wget http://download.opensuse.org/repositories/security:shibboleth/CentOS_7/security:shibboleth.repo
yum --assumeyes update

# basic dependencies
yum --assumeyes install \
    ant cifs-utils clang crontabs gcc-c++.x86_64 git glibc-static make sudo \
    boost-devel ca-certificates curl-openssl file-devel kyotocabinet-devel leptonica libarchive-devel libcurl-openssl-devel libuuid-devel libwebp libxml2-devel.x86_64 libxml2 lsof lz4 mariadb-devel.x86_64 mawk openjpeg-libs openssl-devel pcre-devel policycoreutils-python poppler poppler-utils tokyocabinet-devel unzip \
    tesseract tesseract-devel tesseract-langpack-bul tesseract-langpack-ces tesseract-langpack-dan tesseract-langpack-deu tesseract-langpack-fin tesseract-langpack-fra tesseract-langpack-grc tesseract-langpack-heb tesseract-langpack-hun tesseract-langpack-ita tesseract-langpack-lat tesseract-langpack-nld tesseract-langpack-nor tesseract-langpack-pol tesseract-langpack-por tesseract-langpack-rus tesseract-langpack-slv tesseract-langpack-spa tesseract-langpack-swe

# in CentOS, there is no "tesseract-langpack-eng", it seems to be part of the default installation


### TUEFIND ###
if [[ $1 == "tuefind" ]]; then
    ColorEcho "installing/updating tuefind dependencies..."

    yum --assumeyes install \
        java-*-openjdk-devel \
        httpd mariadb mariadb-server mod_ssl

    # special handling for php+composer: standard php needs to be replaced by php71w
    # (standard is installed as dependancy)
    if yum list installed php71w-common | grep --quiet php71w-common; then
        ColorEcho "PHP 7.1 already installed"
    else
        ColorEcho "replacing standard PHP with PHP 7.1"
        rpm -Uvh https://mirror.webtatic.com/yum/el7/webtatic-release.rpm
        yum --assumeyes remove 'php-*'
        yum --assumeyes install php71w-cli php71w-common php71w-devel php71w-gd php71w-intl php71w-ldap php71w-mbstring php71w-mcrypt php71w-mysqlnd php71w-xml mod_php71w
        systemctl restart httpd
    fi

    # composer also needs to be installed manually to avoid php dependency problems
    if [ -e /usr/local/bin/composer ]; then
        ColorEcho "composer already installed"
    else
        ColorCcho "installing composer"
        wget --output-document=/tmp/composer-setup.php https://getcomposer.org/installer
        php /tmp/composer-setup.php --install-dir=/usr/local/bin --filename=composer
    fi
fi

ColorEcho "finished installing/updating dependencies"
