#!/usr/bin/env bash

ROOT=`dirname "$0"`

# A list of directories which contain wasm projects.
SRCS=(
	"polkadot/runtime/wasm"
	"substrate/executor/wasm"
	"demo/runtime/wasm"
	"substrate/test-runtime/wasm"
	"polkadot/parachain/test-chains/basic_add"
)

# Make pushd/popd silent.

pushd () {
	command pushd "$@" > /dev/null
}

popd () {
	command popd "$@" > /dev/null
}
