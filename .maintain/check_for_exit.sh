#!/usr/bin/env bash

# Script that checks that a node exits after `SIGINT` was send.

set -e

cargo build --release
./target/release/substrate --dev &
PID=$!

# Let the chain running for 60 seconds
sleep 60

# Send `SIGINT` and give the process 30 seconds to end
kill -INT $PID
timeout 30 tail --pid=$PID -f /dev/null
