#!/usr/bin/env bash

set -eux

# Install rustup and the specified rust toolchain.
curl https://sh.rustup.rs -sSf | sh -s -- --default-toolchain=$RUST_TOOLCHAIN -y

# Load cargo environment. Specifically, put cargo into PATH.
source ~/.cargo/env

rustc --version
rustup --version
cargo --version

sudo apt-get -y update
sudo apt-get install -y cmake pkg-config libssl-dev

case $TARGET in
	"checked_in_runtime")
		cargo test --all
		;;

	"rebuild_runtime")
		# NOTE this build target requires nightly compiler.

		# Install prerequisites and build all wasm projects
		./init.sh
		./build.sh

		cargo test --all
		;;
esac
