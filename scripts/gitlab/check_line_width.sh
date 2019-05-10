#!/bin/sh
#
# check if line width of rust source files is not beyond x characters
#


BASE_BRANCH="origin/master"
LINE_WIDTH="101"


FAIL=""

git diff --name-only ${BASE_BRANCH}...${CI_COMMIT_SHA} \*.rs | while read file
do
  if git diff ${BASE_BRANCH}...${CI_COMMIT_SHA} \
    | grep -q "^.\{${LINE_WIDTH}\}" ${file}
  then
    if [ -z "${FAIL}" ]
    then
      echo "| warning!"
	  echo "| Lines should be longer than 100 characters long only in exceptional circumstances and\
 certainly no longer than 120."
	  echo "| "
	  echo "| see more https://wiki.parity.io/Substrate-Style-Guide"
      echo "|"
      FAIL="true"
    fi
    echo "| file: ${file}"
    git diff ${BASE_BRANCH}...${CI_COMMIT_SHA} \
      | grep -n "^.\{${LINE_WIDTH}\}" ${file}
    echo "|"
  fi
done

test "${FAIL}" && exit 1

