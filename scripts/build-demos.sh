#!/usr/bin/env bash

# This script assumes that all pre-requisites are installed.

set -e

PROJECT_ROOT=`git rev-parse --show-toplevel`
source `dirname "$0"`/common.sh

export CARGO_INCREMENTAL=0

# Save current directory.
pushd .

cd $ROOT

for DEMO in "${DEMOS[@]}"
do
  echo "*** Building wasm binaries in $DEMO"
  cd "$PROJECT_ROOT/$DEMO"

  ./build.sh

  cd - >> /dev/null
done

# Restore initial directory.
popd
