#!/bin/sh
set -e

cargo +nightly build --target=wasm32-unknown-unknown --release
for i in test
do
	wasm-gc target/wasm32-unknown-unknown/release/runtime_$i.wasm target/wasm32-unknown-unknown/release/runtime_$i.compact.wasm
done
