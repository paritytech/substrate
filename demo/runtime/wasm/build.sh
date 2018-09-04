#!/usr/bin/env bash
set -e

cargo +nightly-2018-08-27 build --target=wasm32-unknown-unknown --release
for i in demo_runtime
do
	wasm-gc target/wasm32-unknown-unknown/release/$i.wasm target/wasm32-unknown-unknown/release/$i.compact.wasm
done
