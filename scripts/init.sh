#!/usr/bin/env bash

set -e

echo "*** Initializing WASM build environment"

rustup install stable-2021-11-01

rustup target add wasm32-unknown-unknown --toolchain stable-2021-11-01
