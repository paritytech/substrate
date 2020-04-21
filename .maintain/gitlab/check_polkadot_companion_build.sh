#!/bin/sh
#
# check if a pr is compatible with polkadot companion pr or master if not 
# available
#
# to override one that was just mentioned mark companion pr in the body of the 
# polkadot pr like
#
# polkadot companion: paritytech/polkadot#567
#

. $(dirname $0)/lib.sh



boldcat <<-EOT


check_polkadot_companion_build
==============================

this job checks if there is a string in the description of the pr like

polkadot companion: paritytech/polkadot#567


it will then run cargo check from this polkadot's branch with substrate code
from this pull request. in absence of that string it will check if a polkadot
pr is mentioned and will use the last one instead. if none of the above can be
found it will check if polkadot has a branch of the exact same name than the
substrate's branch. if it can't find anything, it will uses master instead


EOT



SUBSTRATE_PATH=$(pwd)

# Clone the current Polkadot master branch into ./polkadot.
git clone --depth 1 https://github.com/paritytech/polkadot.git
cd polkadot

# either it's a pull request then check for a companion otherwise use 
# polkadot:master
if ! [ "${CI_COMMIT_REF_NAME}" -gt 0 2>/dev/null ]
then
  boldprint "this is pull request no ${prno}"
  companion="$(companion_pr "${CI_COMMIT_REF_NAME}")"
  if [ "${companion}" ]
  then
    boldprint "detected companion ref ${companion}"
    git fetch --depth 1 origin "${companion}:companion"
    git checkout companion
  else
    boldprint "companion pr not found - building polkadot:master"
  fi
else
  boldprint "this is not a pull request - building polkadot:master"
fi




# Make sure we override the crates in native and wasm build
# patching the git path as described in the link below did not test correctly
# https://doc.rust-lang.org/cargo/reference/overriding-dependencies.html
mkdir .cargo
echo "paths = [ \"$SUBSTRATE_PATH\" ]" > .cargo/config

mkdir -p target/debug/wbuild/.cargo
cp .cargo/config target/debug/wbuild/.cargo/config

# package, others are updated along the way.
cargo update

# Test Polkadot pr or master branch with this Substrate commit.
time cargo test --all --release --verbose

