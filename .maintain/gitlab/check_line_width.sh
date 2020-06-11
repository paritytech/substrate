#!/bin/sh
#
# check if line width of rust source files is not beyond x characters
#
set -e
set -o pipefail

LINE_WIDTH="120"
GOOD_LINE_WIDTH="100"

if [ -z $CI_COMMIT_BEFORE_SHA ]; then
  echo "No ancestor commit set in \$CI_COMMIT_BEFORE_SHA"
  exit -1;
fi

git diff --name-only ${CI_COMMIT_BEFORE_SHA} -- \*.rs | ( while read file
do
  if [ ! -f ${file} ];
  then
	echo "Skipping removed file."
  elif git diff ${CI_COMMIT_BEFORE_SHA} -- ${file} | grep -q "^+.\{$(( $LINE_WIDTH + 1 ))\}"
  then
    if [ -z "${FAIL}" ]
    then
      echo "| error!"
      echo "| Lines must not be longer than ${LINE_WIDTH} characters."
      echo "| "
      echo "| see more https://wiki.parity.io/Substrate-Style-Guide"
      echo "|"
      FAIL="true"
    fi
    echo "| file: ${file}"
    git diff ${CI_COMMIT_BEFORE_SHA} -- ${file} \
      | grep -n "^+.\{$(( $LINE_WIDTH + 1))\}"
    echo "|"
  else
    if git diff ${CI_COMMIT_BEFORE_SHA} -- ${file} | grep -q "^+.\{$(( $GOOD_LINE_WIDTH + 1 ))\}"
    then
      if [ -z "${FAIL}" ]
      then
        echo "| warning!"
        echo "| Lines should be longer than ${GOOD_LINE_WIDTH} characters only in exceptional circumstances!"
        echo "| "
        echo "| see more https://wiki.parity.io/Substrate-Style-Guide"
        echo "|"
      fi
      echo "| file: ${file}"
      git diff ${CI_COMMIT_BEFORE_SHA} -- ${file} | grep -n "^+.\{$(( $GOOD_LINE_WIDTH + 1 ))\}"
      echo "|"
    fi
  fi
done

test -z "${FAIL}"
)
