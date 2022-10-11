#!/usr/bin/env bash

set -e

echo "*** Initializing Test environment"

rustup install nightly-2021-09-12

rustup target add wasm32-unknown-unknown --toolchain nightly-2021-09-12