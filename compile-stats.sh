#!/bin/bash

set -euo pipefail

WHAT=(
	"Core_execute_block"
	"Core_version"
	"Core_authorities"
	"Core_initialise_block"
	#"BlockBuilder_check_inherents"
	"BlockBuilder_apply_extrinsic"
	"BlockBuilder_finalise_block"
	"BlockBuilder_inherent_extrinsics"
	#"BlockBuilder_random_seed"
	"AuraApi_slot_duration"
	"GrandpaApi_grandpa_authorities"
	"GrandpaApi_grandpa_pending_change"
	#"TaggedTransactionQueue_validate_transaction"
	"Metadata_metadata"
)
for w in ${WHAT[@]};
do
	OUTPUT=""
	RUST_NATIVE=""

	MIN_MEASURES=0
	COMPARE="rust_native wasm2c_wo_bc wasm2c wasmi"
	for c in $COMPARE;
	do
		MEASURES=$(cat /tmp/$c | \
			grep --text "duration" | \
			grep "$w")

		if [[ $MEASURES == 0 ]];
		then
			echo "Too few measurements!"
			exit 1
		fi

		AVG=$(echo "$MEASURES" | \
			cut -d ' ' -f 4 | \
			tr -d 'µs' | \
			awk '{ total += $0; count++ } END { print total/count }')

		if [[ $c == "rust_native" ]];
		then
			RUST_NATIVE="$AVG"
			PCT=100
		fi
		if [[ $c != "rust_native" ]];
		then
			PCT=$(node -e "console.log(($RUST_NATIVE / $AVG) * 100)")
		fi

		LINE=$(printf "%13s: %10.0f µs (%1.1f%%)" $c $AVG $PCT)
                OUTPUT="$OUTPUT$LINE\n"
	done
	echo "# $w"
	echo -e "$OUTPUT"
done
