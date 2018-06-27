#!/usr/bin/env bash

cp polkadot/runtime/wasm/target/wasm32-unknown-unknown/release/polkadot_runtime.compact.wasm polkadot/runtime/wasm/genesis.wasm
cp substrate/test-runtime/wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm substrate/test-runtime/wasm/genesis.wasm
