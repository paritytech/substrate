#!/usr/bin/env bash
set -e

# Make LLD produce a binary that imports memory from the outside environment.
export RUSTFLAGS="-C link-arg=--import-memory"

cargo +nightly build --target=wasm32-unknown-unknown --release --no-default-features

for i in basic_add
do
	wasm-gc target/wasm32-unknown-unknown/release/$i.wasm target/wasm32-unknown-unknown/release/$i.compact.wasm
done
