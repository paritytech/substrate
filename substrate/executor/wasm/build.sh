#!/bin/sh
set -e

cargo +nightly build --target=wasm32-unknown-unknown --release
for i in test
do
	# Add export of the default table under name 'table'.
	wasm-export-table target/wasm32-unknown-unknown/release/runtime_$i.wasm target/wasm32-unknown-unknown/release/runtime_$i.table.wasm
	cp target/wasm32-unknown-unknown/release/runtime_$i.table.wasm target/wasm32-unknown-unknown/release/runtime_$i.wasm
	wasm-gc target/wasm32-unknown-unknown/release/runtime_$i.wasm target/wasm32-unknown-unknown/release/runtime_$i.compact.wasm
done
