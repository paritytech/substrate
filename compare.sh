#!/bin/bash
# 
# Execute
#
#   cargo run --release -- purge-chain -y --chain=dev && cargo run --release -- --dev > /tmp/log 2>&1
#   cat /tmp/log | grep "duration for" > master.numbers
#
# for each version which you want to test.

set -eu pipefail

DATAPOINTS=$(cat master.numbers | cut -d '"' -f 2 | sort | uniq)

for d in $DATAPOINTS; do
	echo "$d:"
	MASTER=$(cat master.numbers | grep $d | cut -d ' ' -f 4 | egrep --only-matching '[0-9]*' | awk '{ total += $1; count++ } END { print total/count }'| cut -d '.' -f 1)
	POOL=$(cat pool.numbers | grep $d | cut -d ' ' -f 4 | egrep --only-matching '[0-9]*' | awk '{ total += $1; count++ } END { print total/count }'  | cut -d '.' -f 1)
	CLONE=$(cat clone.numbers | grep $d | cut -d ' ' -f 4 | egrep --only-matching '[0-9]*' | awk '{ total += $1; count++ } END { print total/count }'  | cut -d '.' -f 1)
	PCT_POOL=$(node -e "console.log(($POOL / $MASTER) * 100)" | cut -d '.' -f 1)
	PCT_CLONE=$(node -e "console.log(($CLONE / $MASTER) * 100)" | cut -d '.' -f 1)

	printf "%-10s %-4s µs (%s)\n" "master:" $MASTER "100%"
	printf "%-10s %-4s µs (%s)\n" "clone:" $CLONE "$PCT_CLONE%"
	printf "%-10s %-4s µs (%s)\n" "pool:" $POOL "$PCT_POOL%"
	echo ""
done
