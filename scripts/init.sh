#!/usr/bin/env bash

set -e

echo "*** Initialising WASM build environment"

rustup update nightly
rustup target add wasm32-unknown-unknown --toolchain nightly
rustup update stable

# Install wasm-gc. It's useful for stripping slimming down wasm binaries.
command -v wasm-gc || \
	cargo +nightly install --git https://github.com/alexcrichton/wasm-gc
