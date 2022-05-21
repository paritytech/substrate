#!/bin/bash

set -e

# Runs all benchmarks for all pallets, for the Substrate node.
# Should be run on a reference machine to gain accurate benchmarks
# current reference machine: https://github.com/paritytech/substrate/pull/5848

echo "[+] Running all benchmarks for Substrate"

cargo +nightly build --profile production --locked --features=runtime-benchmarks

./target/production/substrate benchmark pallet \
    --chain=dev \
    --list |\
  tail -n+2 |\
  cut -d',' -f1 |\
  uniq > "substrate_pallets"

# For each pallet found in the previous command, run benches on each function
while read -r line; do
  pallet="$(echo "$line" | cut -d' ' -f1)";
  folder_name="$(echo "${pallet#*_}" | tr '_' '-')";
  echo "Pallet: $pallet, Folder Name: $folder_name";
  # '!' has the side effect of bypassing errexit / set -e
  ! ./target/production/substrate benchmark pallet \
    --chain=dev \
    --steps=1 \
    --repeat=1 \
    --pallet="$pallet" \
    --extrinsic="*" \
    --execution=wasm \
    --wasm-execution=compiled \
    --template=./.maintain/frame-weight-template.hbs \
    --output="./frame/${folder_name}/src/weights.rs"
done < "substrate_pallets"
rm "substrate_pallets"

# Benchmark base weights
! ./target/production/substrate benchmark overhead \
  --chain=dev \
  --execution=wasm \
  --wasm-execution=compiled \
  --weight-path="./frame/support/src/weights/" \
  --warmup=10 \
  --repeat=100


# This true makes sure that $? is 0 instead of
# carrying over a failure which would otherwise cause
# the whole CI job to abort.
true
