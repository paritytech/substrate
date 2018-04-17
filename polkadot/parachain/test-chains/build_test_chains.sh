#!/bin/sh
set -e

rm -rf ./target
for i in */
do
  i=${i%/}
  cd $i/wasm
  cargo build --target=wasm32-unknown-unknown --release --no-default-features
  wasm-build --target wasm32-unknown-unknown ./target $i
  mv ./target/$i.wasm test.wasm
  cd ../..
done
