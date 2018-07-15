#!/usr/bin/env bash
set -e

RUSTFLAGS="-C link-arg=--export-table" cargo +nightly build --target=wasm32-unknown-unknown --release
for i in test
do
	cp target/wasm32-unknown-unknown/release/runtime_$i.table.wasm target/wasm32-unknown-unknown/release/runtime_$i.wasm
	wasm-gc target/wasm32-unknown-unknown/release/runtime_$i.wasm target/wasm32-unknown-unknown/release/runtime_$i.compact.wasm
done
