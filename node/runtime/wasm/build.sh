#!/usr/bin/env bash
set -e

if cargo --version | grep -q "nightly"; then
	CARGO_CMD="cargo"
else
	CARGO_CMD="cargo +nightly"
fi
$CARGO_CMD rustc --target=wasm32-unknown-unknown --release -- -Z print-link-args -C link-arg='-z stack-size=65536'
for i in node_runtime
do
	wasm-gc target/wasm32-unknown-unknown/release/$i.wasm target/wasm32-unknown-unknown/release/$i.compact.wasm
done
