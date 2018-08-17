#!/usr/bin/env bash

set -eux

case $TARGET in
	"native")
		sudo apt-get -y update
		sudo apt-get install -y cmake pkg-config libssl-dev

		cargo test --all --locked
		;;

	"wasm")
		# Install prerequisites and build all wasm projects
		./scripts/init.sh
		./scripts/build.sh
		./scripts/build-demos.sh
		;;
esac
