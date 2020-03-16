#!/bin/sh
#
# check if a pr is compatible with polkadot companion pr or master if not 
# available


SUBSTRATE_PATH=$(pwd)

# Clone the current Polkadot master branch into ./polkadot.
git clone --depth 1 https://gitlab.parity.io/parity/polkadot.git

cd polkadot
# Make sure we override the crates in native and wasm build
mkdir .cargo
echo "paths = [ \"$SUBSTRATE_PATH\" ]" > .cargo/config
mkdir -p target/debug/wbuild/.cargo
echo "paths = [ \"$SUBSTRATE_PATH\" ]" > target/debug/wbuild/.cargo/config

# package, others are updated along the way.
cargo update

# Check whether Polkadot 'master' branch builds with this Substrate commit.
time cargo check


