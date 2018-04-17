#!/bin/sh
set -e

for i in */
do
  cd $i
  cargo build --target=wasm32-unknown-unknown --release --no-default-features
  mv target/wasm32-unknown-unknown/release/${i%/}.wasm test.wasm
  cd ..
done
