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

wait_port() {
	TIMES=${1:=180}
	PORT=${2:=10710}

	while ! nc -z localhost $PORT && [[ $TIMES -ne 0 ]]; do
		TIMES=$(( TIMES - 1 ))
		sleep 1
	done

	if [[ $TIMES == 0 ]]; then
	   return 1;
	else
		return 0;
	fi

}

trap cleanup SIGINT SIGTERM EXIT

pushd remote-keystore
echo "Building keystore"
cargo build --bin server --features server
popd

(
	cd remote-keystore

	echo "Running keystore"
	set RUST_LOG=debug

	cargo run --bin server --features server
) &

echo "Build substrate executable"
make substrate

if wait_port 60; then
	echo "Unable to start keystore"
	exit 2
fi

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
