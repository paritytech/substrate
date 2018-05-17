#!/bin/sh

rustup update nightly
rustup target add wasm32-unknown-unknown --toolchain nightly
rustup update stable
cargo +nightly install --git https://github.com/alexcrichton/wasm-gc
cargo +nightly install --git https://github.com/pepyakin/wasm-export-table.git
