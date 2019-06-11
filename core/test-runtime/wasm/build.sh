#!/usr/bin/env bash
set -e

CARGO_INCREMENTAL=0 RUSTFLAGS="-C link-arg=--export-table" cargo +nightly build --target=wasm32-unknown-unknown --release "$@"
for i in substrate_test_runtime
do
	wasm-gc "target/wasm32-unknown-unknown/release/$i.wasm" "target/wasm32-unknown-unknown/release/$i.compact.wasm"
done
