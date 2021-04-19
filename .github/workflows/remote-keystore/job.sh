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

if wait_port 60; then
	echo "-------------------- UNABLE TO CONNECT TO KEYSTORE --------------------------"
	exit 2
fi

echo "------------------------ KEYSTORE AVAILABLE ------------------------------"

echo "Running node"
./target/release/substrate --chain zondaxSpecRaw.json --tmp \
	--port 30333 --ws-port 9945 --validator --execution native \
	--node-key 0000000000000000000000000000000000000000000000000000000000000001 --keystore-uri "localhost:10710"&> bootnode.out &

(tail -n +1 -F bootnode.out) &

tail -n +1 -F bootnode.out | timeout 90 grep -E -m 1 "finalized #[1-9][0-9]?"
SUCCESS=$?

if [ $SUCCESS == 141 ] || [ $SUCCESS == 0 ] ; then
	echo "------------------------ BLOCK FINALIZED SUCCESFULLY ----------------------"
	exit 0
else
	echo "---------------------- BLOCK FINALIZATION TIMED OUT/ERRORED ----------------------"
	exit 1
fi
