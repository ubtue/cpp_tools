#!/bin/bash
#
LATEST_CONTAINER_ID=$(docker ps -alq --filter ancestor=zts)
if [ -z "$LATEST_CONTAINER_ID" ]; then
	echo "run new container"
	docker run -p 1969:1969 -d zts
else
	echo "reuse existing container $LATEST_CONTAINER_ID"
	docker start $LATEST_CONTAINER_ID
fi
