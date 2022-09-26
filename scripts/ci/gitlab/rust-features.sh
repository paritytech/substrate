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

#######################################################################
#
# This script checks that no crate enables a specific feature in its
# `default` feature set. It's important to check that since features
# are used to gate specific functionality which should only be enabled
# if the feature is present.
#
# Invocation scheme:
# 	./rust-features.sh <CARGO-ROOT-PATH>
#
# The steps of this script:
#   1. Check that all required dependencies are installed.
#   2. Check that all rules are fullfilled for the whole workspace. If not:
#   4. Check all crates to find the offending ones.
#   5. Print all offending crates and exit with failure.
#
#######################################################################

set -eu

# Check that cargo, grep and egrep are installed.
command -v cargo >/dev/null 2>&1 || { echo >&2 "cargo is required but not installed. Aborting."; exit 1; }
command -v grep >/dev/null 2>&1 || { echo >&2 "grep is required but not installed. Aborting."; exit 1; }
command -v egrep >/dev/null 2>&1 || { echo >&2 "egrep is required but not installed. Aborting."; exit 1; }

SUBSTRATE_ROOT=$1
declare -a RULES=(
	"default,std never implies runtime-benchmarks"
	"default,std never implies try-runtime"
)

function check_does_not_imply() {
	ENABLED=$1
	STAYS_DISABLED=$2
	echo "📏 Checking that $ENABLED does not imply $STAYS_DISABLED ..."

	RET=0
	# Check if the forbidden feature is enabled anywhere in the workspace.
	cargo tree --no-default-features --locked --workspace -e features --features "$ENABLED" | grep -q "feature \"$STAYS_DISABLED\"" || RET=$?
	if [ $RET -ne 0 ]; then
		echo "✅ $ENABLED does not imply $STAYS_DISABLED in the workspace"
		return
	else
		echo "❌ $ENABLED implies $STAYS_DISABLED in the workspace"
	fi

	# Find all Cargo.toml files but exclude the root one since we know that it is broken.
	CARGOS=`find $SUBSTRATE_ROOT -name Cargo.toml -not -path "$SUBSTRATE_ROOT/Cargo.toml"`
	FAILED=0
	PASSED=0
	# number of all cargos
	echo "🔍 Checking individual crates - this takes some time."

	for CARGO in $CARGOS; do
		RET=0
		OUTPUT=$(cargo tree --no-default-features --locked -e features --features $ENABLED --manifest-path $CARGO 2>&1 || true)
		IS_NOT_SUPPORTED=$(echo $OUTPUT | grep -q "not supported for packages in this workspace" || echo $?)

		if [ $IS_NOT_SUPPORTED -eq 0 ]; then
			# This case just means that the pallet does not support the
			# requested feature which is fine.
			PASSED=$((PASSED+1))
		elif echo "$OUTPUT" | grep -q "feature \"$STAYS_DISABLED\""; then
			echo "❌ Violation in $CARGO enabled by dependency"
			# Best effort hint for which dependency needs to be fixed.
			echo "$OUTPUT" | grep -w "feature \"$STAYS_DISABLED\"" | head -n 1
			FAILED=$((FAILED+1))
		else
			PASSED=$((PASSED+1))
		fi
	done

	TOTAL=$((PASSED + FAILED))
	echo "Checked $TOTAL crates in total of which $FAILED failed and $PASSED passed."
	echo "Exiting with code 1"
	exit 1
}

cd "$SUBSTRATE_ROOT"

for RULE in "${RULES[@]}"; do
    read -a splits <<< "$RULE"
	ENABLED=${splits[0]}
	STAYS_DISABLED=${splits[3]}
	# Split ENABLED at , and check each one.
	IFS=',' read -ra ENABLED_SPLIT <<< "$ENABLED"
	for ENABLED_SPLIT in "${ENABLED_SPLIT[@]}"; do
		check_does_not_imply "$ENABLED_SPLIT" "$STAYS_DISABLED"
	done	
done
