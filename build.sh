#!/bin/sh

cd substrate/executor/wasm && ./build.sh && cd ../../..
cd substrate/test-runtime/wasm && ./build.sh && cd ../../..
cd polkadot/runtime/wasm && ./build.sh && cd ../../..
cd demo/runtime/wasm && ./build.sh && cd ../../..
