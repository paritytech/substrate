#!/bin/sh
#
# check if line width of rust source files is not beyond x characters
#
set -e
set -o pipefail

BASE_ORIGIN="origin"
BASE_BRANCH_NAME="master"
LINE_WIDTH="120"
GOOD_LINE_WIDTH="100"
BASE_BRANCH="${BASE_ORIGIN}/${BASE_BRANCH_NAME}"
git fetch ${BASE_ORIGIN} ${BASE_BRANCH_NAME} --depth 100
BASE_HASH=$(git merge-base ${BASE_BRANCH} HEAD)

git diff --name-only ${BASE_HASH} -- \*.rs | ( while read file
do
  if [ ! -f ${file} ];
  then
	echo "Skipping removed file."
  elif git diff ${BASE_HASH} -- ${file} | grep -q "^+.\{$(( $LINE_WIDTH + 1 ))\}"
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
    git diff ${BASE_HASH} -- ${file} \
      | grep -n "^+.\{$(( $LINE_WIDTH + 1))\}"
    echo "|"
  else
    if git diff ${BASE_HASH} -- ${file} | grep -q "^+.\{$(( $GOOD_LINE_WIDTH + 1 ))\}"
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
      git diff ${BASE_HASH} -- ${file} | grep -n "^+.\{$(( $GOOD_LINE_WIDTH + 1 ))\}"
      echo "|"
    fi
  fi
done

test -z "${FAIL}"
)
