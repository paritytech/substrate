#!/usr/bin/env bash
set -e

cargo +nightly build --target=wasm32-unknown-unknown --release
for i in polkadot_runtime
do
	wasm-gc target/wasm32-unknown-unknown/release/$i.wasm target/wasm32-unknown-unknown/release/$i.compact.wasm
done
