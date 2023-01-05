#!/usr/bin/env bash
set -e

pushd .

# The following lines ensure we run from the project root
DOCKER_DIR=$(realpath "$(dirname "${BASH_SOURCE[0]}")")
PROJECT_ROOT=$(dirname "$DOCKER_DIR")

cd $PROJECT_ROOT

# Find the current version from Cargo.toml
VERSION=`grep "^version" ./bin/node/cli/Cargo.toml | egrep -o "([0-9\.]+)"`
GITUSER=parity
GITREPO=substrate

# Build the image
echo "Building ${GITUSER}/${GITREPO}:latest docker image, hang on!"
time DOCKER_BUILDKIT=1 docker build -f ./docker/substrate_builder.Dockerfile -t ${GITUSER}/${GITREPO}:latest .
docker tag ${GITUSER}/${GITREPO}:latest ${GITUSER}/${GITREPO}:v${VERSION}

# Show the list of available images for this repo
echo "Image is ready"
docker images | grep ${GITREPO}

popd
