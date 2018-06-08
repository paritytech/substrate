#!/bin/sh

# NOTE `cargo install wasm-gc` before running this script.
# NOTE `cargo install --git https://github.com/pepyakin/wasm-export-table.git`

set -e
export CARGO_INCREMENTAL=0

cd demo/runtime/wasm && ./build.sh && cd ../../..
cd substrate/executor/wasm && ./build.sh && cd ../../..
cd substrate/test-runtime/wasm && ./build.sh && cd ../../..
cd polkadot/runtime/wasm && ./build.sh && cd ../../..
cd polkadot/parachain/test-chains && ./build.sh && cd ../../..
