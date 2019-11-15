#!/usr/bin/env bash

SINGLE_DATES=$(grep -lr "// Copyright [0-9]* Parity Technologies (UK) Ltd.")
RANGE_DATES=$(grep -lr "// Copyright [0-9]*-[0-9]* Parity Technologies (UK) Ltd.")
YEAR=$(date +%Y)

for file in $SINGLE_DATES; do
  FILE_YEAR=$(cat $file | sed -n "s|// Copyright \([[:digit:]][[:digit:]][[:digit:]][[:digit:]]\) Parity Technologies (UK) Ltd.|\1|p")
  if [ $YEAR -ne $FILE_YEAR ]; then
    sed -i -e "s|// Copyright \([[:digit:]][[:digit:]][[:digit:]][[:digit:]]\) Parity Technologies (UK) Ltd.|// Copyright \1-$YEAR Parity Technologies (UK) Ltd.|g" $file
  fi
done

grep -lr "// Copyright [0-9]*-[0-9]* Parity Technologies (UK) Ltd." |
  xargs sed -i -e "s|// Copyright \([[:digit:]][[:digit:]][[:digit:]][[:digit:]]\)-[[:digit:]][[:digit:]][[:digit:]][[:digit:]] Parity Technologies (UK) Ltd.|// Copyright \1-$YEAR Parity Technologies (UK) Ltd.|g"
