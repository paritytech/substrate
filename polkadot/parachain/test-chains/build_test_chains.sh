#!/bin/sh
set -e

rm -rf ./target
for i in */
do
  i=${i%/}
  cd $i

  # TODO: stop using exact nightly when wee-alloc works on normal nightly.
  RUSTFLAGS="-C link-arg=--import-memory" cargo +nightly-2018-03-07 build --target=wasm32-unknown-unknown --release --no-default-features
  wasm-gc target/wasm32-unknown-unknown/release/$i.wasm ../../tests/res/$i.wasm
  cd ..
done
