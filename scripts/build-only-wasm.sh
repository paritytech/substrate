#!/usr/bin/env sh

# Script for building only the WASM binary of the given project.

set -e

PROJECT_ROOT=`git rev-parse --show-toplevel`

if [ "$#" -lt 1 ]; then
  echo "You need to pass the name of the crate you want to compile!"
  exit 1
fi

WASM_BUILDER_RUNNER="$PROJECT_ROOT/target/release/wbuild-runner/$1"

if [ -z "$2" ]; then
  export WASM_TARGET_DIRECTORY=$(pwd)
else
  export WASM_TARGET_DIRECTORY=$2
fi

if [ -d $WASM_BUILDER_RUNNER ]; then
  export DEBUG=false
  export OUT_DIR="$PROJECT_ROOT/target/release/build"
  cargo run --release --manifest-path="$WASM_BUILDER_RUNNER/Cargo.toml" \
    | grep -vE "cargo:rerun-if-|Executing build command"
else
  cargo build --release -p $1
fi
