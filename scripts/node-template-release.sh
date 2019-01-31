#!/usr/bin/env bash

set -e

PROJECT_ROOT=`git rev-parse --show-toplevel`

if [ "$#" -ne 1 ]; then
  echo "node-template-release.sh path_to_target_archive"
  exit 1
fi

PATH_TO_ARCHIVE=$(pwd)/$1
cd $PROJECT_ROOT/scripts/node-template-release

echo $PATH_TO_ARCHIVE
cargo run $PROJECT_ROOT/node-template $PATH_TO_ARCHIVE
