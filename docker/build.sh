#!/usr/bin/env bash
set -e

VERSION=`grep "^version" ../Cargo.toml | egrep -o "([0-9\.]+)"`

echo "Building polkadot:$VERSION docker image, hang on!"
docker build --build-arg PROFILE=release -t polkadot:$VERSION .

echo "Image is ready"
docker images | grep polkadot
