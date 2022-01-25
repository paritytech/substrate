#! /bin/bash

remote=${1:-"tcp://10.127.127.151:39946"}

echo "Starting Alice, Bob and Robert"

echo "Robert remote keystore assumed at $remote; Invoke with one argument to change"

(./target/release/substrate --discover-local --chain chainspecs/starSpec.json --tmp --execution native --alice --port /ip4/0.0.0.0/tcp/30333 --ws-port 9944 > alice.out) &
(./target/release/substrate --discover-local --chain chainspecs/starSpec.json --tmp --execution native --bob --port /ip4/0.0.0.0/tcp/30334 --ws-port 9945 >  bob.out) &
(./target/release/substrate --discover-local --chain chainspecs/starSpec.json --tmp --execution native --validator --port /ip4/0.0.0.0/tcp/30335 --ws-port 9946 --keystore-uri $remote > robert.out) &

wait
