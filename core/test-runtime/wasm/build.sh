#!/usr/bin/env bash
set -e

if cargo --version | grep -q "nightly"; then
	CARGO_CMD="cargo"
else
	CARGO_CMD="cargo +nightly"
fi

# Note that we set the stack-size to 1MB explicitly even though it is set
# to this value by default. This is because some of our tests (`restoration_of_globals`)
# depend on the stack-size.
CARGO_INCREMENTAL=0 RUSTFLAGS="-C link-arg=--export-table -C link-arg=-zstack-size=1048576" $CARGO_CMD build --target=wasm32-unknown-unknown --release "$@"
for i in substrate_test_runtime
do
	wasm-gc "target/wasm32-unknown-unknown/release/$i.wasm" "target/wasm32-unknown-unknown/release/$i.compact.wasm"
done
