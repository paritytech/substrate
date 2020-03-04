#!/bin/bash

set -e # fail on any error
set -u # treat unset variables as error

CARGO_WEB_RELEASE=$(curl -L -s -H 'Accept: application/json' https://github.com/koute/cargo-web/releases/latest)
CARGO_WEB_VERSION=$(echo $CARGO_WEB_RELEASE | sed -e 's/.*"tag_name":"\([^"]*\)".*/\1/')
if [ "$(uname -s)" == "Darwin" ]; then
  CARGO_WEB_HOST_TRIPLE="x86_64-apple-darwin"
else
  CARGO_WEB_HOST_TRIPLE="x86_64-unknown-linux-gnu"
fi
CARGO_WEB_URL="https://github.com/koute/cargo-web/releases/download/$CARGO_WEB_VERSION/cargo-web-$CARGO_WEB_HOST_TRIPLE.gz"


echo "Downloading cargo-web from: $CARGO_WEB_URL"
curl -L $CARGO_WEB_URL | gzip -d > cargo-web
chmod +x cargo-web

#mkdir -p ~/.cargo/bin
mv cargo-web /usr/share/rust/.cargo/bin
