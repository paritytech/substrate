#!/usr/bin/env bash
set -e

CARGO_INCREMENTAL=0 RUSTFLAGS="-C link-arg=--export-table" cargo +nightly build --target=wasm32-unknown-unknown --release "$@"
for i in test
do
	wasm-gc "target/wasm32-unknown-unknown/release/runtime_$i.wasm" "target/wasm32-unknown-unknown/release/runtime_$i.compact.wasm"
done
