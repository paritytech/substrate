##
# Zondax Private Testnet
#
# @file
# @version 0.1
.PHONY: all bootnode

substrate:
	SKIP_WASM_BUILD=1 cargo build --bin substrate --release

all:
	cargo build --release

bootnode: substrate
	./target/release/substrate --discover-local --chain chainspecs/zondaxSpec.json --tmp --execution native --validator --keystore-uri "tcp://192.168.88.234:39946" --listen-addr /ip4/0.0.0.0/tcp/30333 --ws-port 9944

othernode: substrate
	./target/release/substrate --discover-local --chain chainspecs/zondaxSpec.json --tmp --execution native --listen-addr /ip4/0.0.0.0/tcp/30334 --ws-port 9945 --alice

# end
