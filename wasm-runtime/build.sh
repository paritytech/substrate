#!/bin/sh

cargo +nightly build --target=wasm32-unknown-unknown --release
dirs=`find * -maxdepth 0 -type d | grep -v pwasm- | grep -v std`
for i in $dirs
do
	if [[ -e $i/Cargo.toml ]]
	then
		wasm-gc target/wasm32-unknown-unknown/release/runtime_$i.wasm target/wasm32-unknown-unknown/release/runtime_$i.compact.wasm
	fi
done
