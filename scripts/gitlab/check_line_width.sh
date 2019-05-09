#!/bin/sh
#
# check if line width of rust source files is not beyond x characters
#


BASE_BRANCH="origin/master"
LINE_WIDTH="101"


if git diff ${BASE_BRANCH}...${CI_COMMIT_SHA} \
  | grep "^.\{${LINE_WIDTH}\}" ${file}
then
  echo "|"
  echo "| newly added lines longer than ${LINE_WIDTH} characters."
  echo "|"
  exit 1
fi


