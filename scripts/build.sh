#!/usr/bin/env bash

# This script assumes that all pre-requisites are installed.

set -e

PROJECT_ROOT=`git rev-parse --show-toplevel`    # /home/tripleight/code/github.com/paritytech/substrate
source "`dirname \"$0\"`/common.sh"             # source scripts/common.sh

export CARGO_INCREMENTAL=0

# Save current directory.
pushd .                                         # PROJECT_ROOT

cd -- "$ROOT"                                   # scripts

for SRC in "${SRCS[@]}"                         # SRCS=("core/executor/wasm" "node/runtime/wasm" "node-template/runtime/wasm"	"core/test-runtime/wasm")
do
  echo "*** Building wasm binaries in $SRC"
  cd "$PROJECT_ROOT/$SRC"                       # 
  
  ./build.sh "$@"

  cd - >> /dev/null
done

# Restore initial directory.
popd                                            # cd $PROJECT_ROOT
