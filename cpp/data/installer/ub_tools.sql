-- under CentOS we still have MariaDB 5, which has a limitation of 767 bytes for keys.
-- this means e.g. for VARCHAR with utf8mb4, we can use at most a VARCHAR(191)!
-- Also, the default collating sequence is a Swedish one.  This leads to aliasing problems for characters with
-- diacritical marks => we need to override it and use utf8mb4_bin.

-- The sizes here must be in sync with the constants defined in rss_aggregator.cc!
CREATE TABLE table_versions (
    version INT UNSIGNED NOT NULL,
    database_name VARCHAR(64) NOT NULL,
    table_name VARCHAR(64) NOT NULL,
    UNIQUE(database_name,table_name)
) CHARACTER SET utf8mb4 COLLATE utf8mb4_bin;

CREATE TABLE rss_aggregator (
    item_id VARCHAR(191) NOT NULL,
    item_url VARCHAR(512) NOT NULL,
    item_title VARCHAR(200) NOT NULL,
    item_description TEXT NOT NULL,
    serial_name VARCHAR(200) NOT NULL,
    feed_url VARCHAR(512) NOT NULL,
    pub_date DATETIME NOT NULL,
    insertion_time TIMESTAMP DEFAULT NOW() NOT NULL,
    UNIQUE (item_id)
) CHARACTER SET utf8mb4 COLLATE utf8mb4_bin;
CREATE INDEX item_id_index ON rss_aggregator(item_id);
CREATE INDEX item_url_index ON rss_aggregator(item_url);
CREATE INDEX insertion_time_index ON rss_aggregator(insertion_time);

-- Table to be used w/ our validate_harvested_records tool:
CREATE TABLE metadata_presence_tracer (
       journal_name VARCHAR(191) NOT NULL,
       metadata_field_name VARCHAR(191) NOT NULL,
       field_presence ENUM('always', 'sometimes', 'ignore') NOT NULL,
       UNIQUE(journal_name, metadata_field_name)
) CHARACTER SET utf8mb4 COLLATE utf8mb4_bin;
CREATE INDEX journal_name_and_metadata_field_name_index ON metadata_presence_tracer(journal_name, metadata_field_name);


CREATE TABLE delivered_marc_records (
    id INT AUTO_INCREMENT PRIMARY KEY,
    url VARCHAR(191) NOT NULL,
    hash VARCHAR(40) NOT NULL,
    zeder_id VARCHAR(10) NOT NULL,
    delivered_at TIMESTAMP NOT NULL DEFAULT NOW(),
    journal_name VARCHAR(191) NOT NULL,
    main_title VARCHAR(191) NOT NULL,
    publication_year CHAR(4) DEFAULT NULL,
    volume CHAR(40) DEFAULT NULL,
    issue CHAR(40) DEFAULT NULL,
    pages CHAR(20) DEFAULT NULL,
    resource_type ENUM('print','online','unknown') NOT NULL,
    record BLOB NOT NULL
) CHARACTER SET utf8mb4 COLLATE utf8mb4_bin;
CREATE INDEX delivered_marc_records_url_index ON delivered_marc_records(url);
CREATE INDEX delivered_marc_records_hash_index ON delivered_marc_records(hash);
CREATE INDEX delivered_marc_records_zeder_id_index ON delivered_marc_records(zeder_id);
CREATE INDEX delivered_marc_records_delivered_at_index ON delivered_marc_records(delivered_at);
CREATE INDEX delivered_marc_records_journal_name_index ON delivered_marc_records(journal_name);
CREATE INDEX delivered_marc_records_main_title_index ON delivered_marc_records(main_title);

CREATE TABLE delivered_marc_records_superior_info (
    zeder_id VARCHAR(10) PRIMARY KEY,
    control_number VARCHAR(20) DEFAULT NULL,
    title VARCHAR(191) NOT NULL,
    CONSTRAINT zeder_id FOREIGN KEY (zeder_id) REFERENCES delivered_marc_records (zeder_id) ON DELETE CASCADE ON UPDATE CASCADE
) CHARACTER SET utf8mb4 COLLATE utf8mb4_bin;
