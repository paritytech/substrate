#!/usr/bin/env bash
set -uo pipefail

# run bootnode and server in parallel
rm bootnode.out
rm remote-keystore/keystore.out
rm tests.out

# This will kill all spawned processes
cleanup() {
	pkill -P $$
}

trap cleanup SIGINT SIGTERM EXIT

(
	echo "Running keystore"
	set RUST_LOG=debug

	cd remote-keystore
	cargo run --bin server --features server &> keystore.out
) &

echo "Build substrate executable"
make substrate

echo "Running node"
make bootnode &> bootnode.out &

(tail -F bootnode.out) &

tail -F bootnode.out | timeout 60 grep -E -m 1 "finalized #[1-9][0-9]?" > tests.out

if [[ ! -s tests.out ]]; then
	echo "---------------------- BLOCK FINALIZATION TIMED OUT ----------------------"
	exit 1
else
	echo "------------------------ BLOCK FINALIZED SUCCESFULLY ----------------------"
	exit 0
fi
