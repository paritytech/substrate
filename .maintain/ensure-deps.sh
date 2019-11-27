#!/usr/bin/env bash

# The script is meant to check if the rules regarding packages
# dependencies are satisfied.
# The general format is:
# [top-lvl-dir] MESSAGE/[other-top-dir]

# For instance no crate within `./client` directory
# is allowed to import any crate with a directory path containing `frame`.
# Such rule is just: `client crates must not depend on anything in /frame`.

# The script should be run from the main repo directory!

set -u

# HARD FAILING
MUST_NOT=(
	"client crates must not depend on anything in /frame"
	"client crates must not depend on anything in /node"
	"frame crates must not depend on anything in /node"
	"frame crates must not depend on anything in /client"
	"primitives crates must not depend on anything in /frame"
)

# ONLY DISPLAYED, script still succeeds
PLEASE_DONT=(
	"primitives crates should not depend on anything in /client"
)

VIOLATIONS=()
PACKAGES=()

function check_rule() {
	rule=$1
	from=$(echo $rule | cut -f1 -d\ )
	to=$(echo $rule | cut -f2 -d\/)

	cd $from
	echo "Checking rule '$rule'"
	packages=$(find -name Cargo.toml | xargs grep -wn "path.*\.\.\/$to")
	has_references=$(echo -n $packages | wc -c)
	if [ "$has_references" != "0" ]; then
		VIOLATIONS+=("$rule")
		# Find packages that violate:
		PACKAGES+=("$packages")
	fi
	cd - > /dev/null
}

for rule in "${MUST_NOT[@]}"
do
	check_rule "$rule";
done

# Only the MUST NOT will be counted towards failure
HARD_VIOLATIONS=${#VIOLATIONS[@]}


for rule in "${PLEASE_DONT[@]}"
do
	check_rule "$rule";
done

# Display violations and fail
I=0
for v in "${VIOLATIONS[@]}"
do
	cat << EOF

===========================================
======= Violation of rule: $v
===========================================
${PACKAGES[$I]}


EOF
	I=$I+1
done

exit $HARD_VIOLATIONS
