#!/usr/bin/env bash

set -e

echo "*** Initializing WASM build environment"

rustup install nightly-2021-03-14

rustup target add wasm32-unknown-unknown --toolchain nightly-2021-03-14
