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
# Has `cargo-workspaces` as optional dependency:
# https://github.com/pksunkara/cargo-workspaces
#
# Invocation scheme:
# 	./rust-features.sh <CARGO-ROOT-PATH>
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
	echo "📏 Checking that '$ENABLED' does not imply '$STAYS_DISABLED'"

	RET=0
	# Check if the forbidden feature is enabled anywhere in the workspace.
	cargo tree --no-default-features --locked --offline --workspace -e features --features "$ENABLED" | grep -q "feature \"$STAYS_DISABLED\"" || RET=$?
	if [ $RET -ne 0 ]; then
		echo "✅ Feature '$ENABLED' does not imply '$STAYS_DISABLED' in the workspace"
		return
	else
		echo "❌ Feature '$ENABLED' implies '$STAYS_DISABLED' in the workspace"
	fi

	# Check if `cargo-workspaces` is installed.
	# If not, the user only gets a generic error instead of a nicer one.
	if ! cargo workspaces --version > /dev/null 2>&1; then
		echo "❌ Install 'cargo-workspaces' for a more detailed error message."
		exit 1
	fi

	CRATES=`cargo workspaces list --all | egrep -o '^(\w|-)+'`
	FAILED=0
	PASSED=0
	echo "🔍 Checking individual crates"

	for CRATE in $CRATES; do
		RET=0
		OUTPUT=$(cargo tree --no-default-features --locked --offline -e features --features $ENABLED -p $CRATE 2>&1 || true)
		IS_NOT_SUPPORTED=$(echo $OUTPUT | grep -q "not supported for packages in this workspace" || echo $?)

		if [ $IS_NOT_SUPPORTED -eq 0 ]; then
			# This case just means that the pallet does not support the
			# requested feature which is fine.
			PASSED=$((PASSED+1))
		elif echo "$OUTPUT" | grep -q "feature \"$STAYS_DISABLED\""; then
			echo "❌ Feature '$ENABLED' implies '$STAYS_DISABLED' in $CRATE; enabled by"
			echo "$OUTPUT" | grep -w "feature \"$STAYS_DISABLED\"" | head -n 1
			FAILED=$((FAILED+1))
		else
			PASSED=$((PASSED+1))
		fi
	done

	TOTAL=$((PASSED + FAILED))
	echo "Checked $TOTAL crates in total of which $FAILED failed and $PASSED passed."

	if [ $FAILED -ne 0 ]; then
		exit 1
	fi
}

cd "$SUBSTRATE_ROOT"

for RULE in "${RULES[@]}"; do
    read -a splits <<< "$RULE"
	check_does_not_imply "${splits[0]}" "${splits[3]}"
done
