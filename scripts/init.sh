#!/usr/bin/env bash

set -e

echo "*** Initializing WASM build environment"

rustup install 1.54.0

rustup target add wasm32-unknown-unknown --toolchain 1.54.0
