#!/bin/bash

set -e # fail on any error
set -u # treat unset variables as error

WASM_PACK_RELEASE=$(curl -L -s -H 'Accept: application/json' https://github.com/rustwasm/wasm-pack/releases/latest)
WASM_PACK_VERSION=$(echo $WASM_PACK_RELEASE | sed -e 's/.*"tag_name":"\([^"]*\)".*/\1/')
if [ "$(uname -s)" == "Darwin" ]; then
  WASM_PACK_HOST_TRIPLE="x86_64-apple-darwin"
else
  WASM_PACK_HOST_TRIPLE="x86_64-unknown-linux-gnu"
fi
WASM_PACK_URL="https://github.com/rustwasm/wasm-pack/releases/download/$WASM_PACK_VERSION/wasm-pack-$WASM_PACK_VERSION-$WASM_PACK_HOST_TRIPLE.tar.gz"


echo "Downloading wasm-pack from: $WASM_PACK_URL"
curl -L $WASM_PACK_URL | tar -xzvf > wasm-pack
chmod +x wasm-pack

#mkdir -p ~/.cargo/bin
mv wasm-pack /usr/share/rust/.cargo/bin
