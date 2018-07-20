#!/usr/bin/env bash
set -e

# Make LLD produce a binary that imports memory from the outside environment.
export RUSTFLAGS="-C link-arg=--import-memory -C lto=fat -C panic=abort"

cargo +nightly build --target=wasm32-unknown-unknown --release --no-default-features --target-dir target

wasm-gc target/wasm32-unknown-unknown/release/basic_add_wasm.wasm target/wasm32-unknown-unknown/release/basic_add.wasm
mv target/wasm32-unknown-unknown/release/basic_add.wasm ../../../parachain/tests/res/
