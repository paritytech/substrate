#!/bin/sh
#
# check if line width of rust source files is not beyond x characters
#


BASE_BRANCH="origin/master"
LINE_WIDTH="121"
GOOD_LINE_WIDTH="101"


FAIL=""

git diff --name-only ${BASE_BRANCH}...${CI_COMMIT_SHA} \*.rs | while read file
do
  if git diff ${BASE_BRANCH}...${CI_COMMIT_SHA} | grep -q "^+.\{${LINE_WIDTH}\}" ${file}
  then
    if [ -z "${FAIL}" ]
    then
      echo "| warning!"
      echo "| Lines should not be longer than 120 characters."
      echo "| "
      echo "| see more https://wiki.parity.io/Substrate-Style-Guide"
      echo "|"
      FAIL="true"
    fi
    echo "| file: ${file}"
    git diff ${BASE_BRANCH}...${CI_COMMIT_SHA} ${file} \
      | grep -n "^+.\{${LINE_WIDTH}\}" ${file}
    echo "|"
  else
    if git diff ${BASE_BRANCH}...${CI_COMMIT_SHA} | grep -q "^+.\{${GOOD_LINE_WIDTH}\}" ${file}
    then
      if [ -z "${FAIL}" ]
      then
        echo "| warning!"
        echo "| Lines should be longer than 100 characters only in exceptional circumstances!"
        echo "| "
        echo "| see more https://wiki.parity.io/Substrate-Style-Guide"
        echo "|"
      fi
      echo "| file: ${file}"
      git diff ${BASE_BRANCH}...${CI_COMMIT_SHA} ${file} \
        | grep -n "^+.\{${LINE_WIDTH}\}" ${file}
      echo "|"
    fi
  fi
done

test "${FAIL}" && exit 1

