#!/usr/bin/env bash

set -e

echo "*** Initilising WASM build environment"

rustup update nightly
rustup target add wasm32-unknown-unknown --toolchain nightly
rustup update stable

# Install wasm-gc. It's useful for stripping slimming down wasm binaries.
command -v wasm-gc || \
	cargo +nightly install --git https://github.com/alexcrichton/wasm-gc

# At the moment of writing, rustc still uses LLD 6 which produces wasm binaries
# that don't export a table. Meanwhile, we are waiting for LLD 7 to come
# in rustc we could use this handy little tool.
command -v wasm-export-table || \
	cargo +nightly install --git https://github.com/pepyakin/wasm-export-table.git
