##
# Zondax Private Testnet
#
# @file
# @version 0.1
.PHONY: all bootnode

substrate:
	cargo build --bin substrate --release

all:
	cargo build --release

ks:
	cd ./extra/tcp-keystore && cargo build --bin server --features server

bootnode: substrate
	./target/release/substrate --chain zondaxSpecRaw.json --tmp --port 30333 --ws-port 9945 --validator --execution native --node-key 0000000000000000000000000000000000000000000000000000000000000001 --keystore-uri "localhost:10710"

othernode: substrate
	./target/release/substrate --chain zondaxSpecRaw.json --tmp --port 30334 --ws-port 9946 --execution native --bootnodes /ip4/127.0.0.1/tcp/30333/p2p/12D3KooWEyoppNCUx8Yx66oV9fJnriXwCcXwDDUA2kj6vnc6iDEp

bootnode_ks: ks
	cd ./extra/tcp-keystore && cargo run --bin server --features server
# end
