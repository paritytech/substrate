#!/usr/bin/env bash
set -e

# Make LLD produce a binary that imports memory from the outside environment.
export RUSTFLAGS="-C link-arg=--import-memory -C lto=fat -C panic=abort"

for i in adder
do
	cd $i/wasm
	cargo +nightly build --target=wasm32-unknown-unknown --release --no-default-features --target-dir target
	wasm-gc target/wasm32-unknown-unknown/release/$i'_'wasm.wasm target/wasm32-unknown-unknown/release/$i.wasm
	cp target/wasm32-unknown-unknown/release/$i.wasm ../../../parachain/tests/res/
	rm -rf target
	cd ../..
done
