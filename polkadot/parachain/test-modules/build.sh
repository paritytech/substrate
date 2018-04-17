#!/bin/sh
set -e

for i in */
do
  cd $i
  cargo build --target=wasm32-unknown-unknown --release
  mv target/wasm32-unknown-unknown/release/${i%/}.wasm ../../tests/res/
  cd ..
done
