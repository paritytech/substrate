#!/bin/sh

cargo +nightly build --target=wasm32-unknown-unknown --release
wasm-gc target/wasm32-unknown-unknown/release/runtime.wasm target/wasm32-unknown-unknown/release/runtime.compact.wasm
