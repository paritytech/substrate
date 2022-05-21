#!/bin/bash

# This file is part of Substrate.
# Copyright (C) 2022 Parity Technologies (UK) Ltd.
# SPDX-License-Identifier: Apache-2.0
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Fail if any sub-command fails.
set -e
# Fail if any sub-command in a pipe fails, not just the last one.
set -o pipefail
# Fail on undeclared variables.
set -u
# Fail on traps.
set -E
# Echo all executed commands.
set -x

# Runs all benchmarks for all pallets, for the Substrate node.
# Should be run on a reference machine to gain accurate benchmarks
# current reference machine: https://github.com/paritytech/substrate/pull/5848

if [ "$1" != "skip-build" ]
then
  echo "[+] Compiling Substrate benchmarks..."
  cargo +nightly build --profile production --locked --features=runtime-benchmarks
fi

# The executable to use.
SUBSTRATE=./target/production/substrate

# Manually exclude some pallets.
EXCLUDED_PALLETS=(
  # Helper pallets
  "pallet_election_provider_support_benchmarking"
  # Pallets without automatic benchmarking
  "pallet_baba"
  "pallet_grandpa"
  "pallet_mmr"
  "pallet_offenes"
)

# Load all pallet names in an array.
ALL_PALLETS=($(
  $SUBSTRATE benchmark pallet --list --dev |\
    tail -n+2 |\
    cut -d',' -f1 |\
    sort |\
    uniq
))

# Filter out the excluded pallets by concatenating the arrays and discarding duplicates.
PALLETS=($({ printf '%s\n' "${ALL_PALLETS[@]}" "${EXCLUDED_PALLETS[@]}"; } | sort | uniq -u))

echo "[+] Benchmarking ${#PALLETS[@]} Substrate pallets by excluding ${#EXCLUDED_PALLETS[@]} from ${#ALL_PALLETS[@]}."

# Benchmark each pallet.
for PALLET in "${PALLETS[@]}"; do
  FOLDER="$(echo "${PALLET#*_}" | tr '_' '-')";
  WEIGHT_FILE="./frame/${FOLDER}/src/weights.rs"
  echo "Pallet: $PALLET, Weight file: $WEIGHT_FILE";

  $SUBSTRATE benchmark pallet \
    --dev \
    --steps=50 \
    --repeat=20 \
    --pallet="$PALLET" \
    --extrinsic="*" \
    --execution=wasm \
    --wasm-execution=compiled \
    --template=./.maintain/frame-weight-template.hbs \
    --output="$WEIGHT_FILE"
done

# Update the block and extrinsic overhead weights.
echo "[+] Benchmarking block and extrinsic overheads..."
$SUBSTRATE benchmark overhead \
  --dev \
  --execution=wasm \
  --wasm-execution=compiled \
  --weight-path="./frame/support/src/weights/" \
  --warmup=10 \
  --repeat=100

echo "[+] Benchmarking the machine..."
$SUBSTRATE benchmark machine --dev
