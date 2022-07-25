#!/usr/bin/env bash
#
# Script for updating the UI tests for a new rust stable version.
#
# It needs to be called like this:
#
# update-rust-stable.sh 1.61
#
# This will run all UI tests with the rust stable 1.61. The script
# requires that rustup is installed.
set -e

if [ "$#" -ne 1 ]; then
	echo "Please specify the rust version to use. E.g. update-rust-stable.sh 1.61"
	exit
fi

RUST_VERSION=$1

if ! command -v rustup &> /dev/null
then
	echo "rustup needs to be installed"
	exit
fi

rustup install $RUST_VERSION
rustup component add rust-src --toolchain $RUST_VERSION

# Ensure we run the ui tests
export RUN_UI_TESTS=1
# We don't need any wasm files for ui tests
export SKIP_WASM_BUILD=1
# Let trybuild overwrite the .stderr files
export TRYBUILD=overwrite

# Run all the relevant UI tests
#
# Any new UI tests in different crates need to be added here as well.
rustup run $RUST_VERSION cargo test -p sp-runtime-interface ui
rustup run $RUST_VERSION cargo test -p sp-api-test ui
rustup run $RUST_VERSION cargo test -p frame-election-provider-solution-type ui
rustup run $RUST_VERSION cargo test -p frame-support-test ui
