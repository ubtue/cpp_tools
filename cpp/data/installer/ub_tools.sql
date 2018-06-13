-- under CentOS we still have MariaDB 5, which has a limitation of 767 bytes for keys.
-- this means e.g. for VARCHAR with utf8mb4, we can use at most a VARCHAR(191)!

-- The sizes here must be in sync with the constants defined in rss_aggregator.cc!
CREATE TABLE rss_aggregator (
    item_id VARCHAR(191) NOT NULL,
    item_url VARCHAR(512) NOT NULL,
    title_and_or_description TEXT NOT NULL,
    serial_name VARCHAR(200) NOT NULL,
    insertion_time TIMESTAMP DEFAULT NOW() NOT NULL,
    UNIQUE (item_id)
) CHARACTER SET utf8mb4;
CREATE INDEX item_id_index ON rss_aggregator(item_id);
CREATE INDEX item_url_index ON rss_aggregator(item_url);
CREATE INDEX insertion_time_index ON rss_aggregator(insertion_time);


CREATE TABLE rss_feeds (
    id INT AUTO_INCREMENT PRIMARY KEY,
    feed_url VARCHAR(191) NOT NULL,
    last_build_date DATETIME NOT NULL,
    UNIQUE (feed_url)
) CHARACTER SET utf8mb4;
CREATE INDEX rss_feeds_ids_index ON rss_feeds(id);
CREATE INDEX rss_feeds_feed_url_index ON rss_feeds(feed_url);


CREATE TABLE rss_items (
    feed_id INT NOT NULL,
    item_id VARCHAR(191) NOT NULL,
    creation_datetime TIMESTAMP NOT NULL DEFAULT NOW(),
    UNIQUE KEY feed_url_and_item_id(feed_id,item_id),
    CONSTRAINT feed_id FOREIGN KEY (feed_id) REFERENCES rss_feeds (id) ON DELETE CASCADE
) CHARACTER SET utf8mb4;

CREATE INDEX rss_items_feed_id_and_item_id_index ON rss_items(feed_id,item_id);
CREATE INDEX rss_items_creation_datetime_index ON rss_items(creation_datetime);
