#!/bin/bash

set -e # fail on any error
set -u # treat unset variables as error

WASM_GC_RELEASE=$(curl -L -s -H 'Accept: application/json' https://github.com/alexcrichton/wasm-gc/releases/latest)
WASM_GC_VERSION=$(echo $WASM_GC_RELEASE | sed -e 's/.*"tag_name":"\([^"]*\)".*/\1/')
if [ "$(uname -s)" == "Darwin" ]; then
  WASM_GC_HOST_TRIPLE="x86_64-apple-darwin"
else
  WASM_GC_HOST_TRIPLE="x86_64-unknown-linux-musl"
fi
WASM_GC_BASENAME="wasm-gc-wasm-gc-$WASM_GC_VERSION-$WASM_GC_HOST_TRIPLE"
WASM_GC_URL="https://github.com/alexcrichton/wasm-gc/releases/download/$WASM_GC_VERSION/$WASM_GC_BASENAME.tar.gz"


echo "Downloading wasm-gc from: $WASM_GC_URL"
curl -LO $WASM_GC_URL
tar -xzvf "$WASM_GC_BASENAME.tar.gz"
cd $WASM_GC_BASENAME
chmod +x wasm-gc

#mkdir -p ~/.cargo/bin
mv wasm-gc /usr/share/rust/.cargo/bin
