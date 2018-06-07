#!/bin/sh
set -e

rm -rf ./target
for i in */
do
  i=${i%/}
  cd $i

  RUSTFLAGS="-C link-arg=--import-memory" cargo +nightly build --target=wasm32-unknown-unknown --release --no-default-features
  wasm-gc target/wasm32-unknown-unknown/release/$i.wasm ../../tests/res/$i.wasm
  cd ..
done
