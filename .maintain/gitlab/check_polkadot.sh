#!/bin/sh
#
# check if a pr is compatible with polkadot companion pr or master if not 
# available
#
# mark companion pr in the body of the polkadot pr like
#
# polkadot companion: paritytech/polkadot#567


github_api_polkadot_pull_url="https://api.github.com/repos/paritytech/polkadot"
# use github api v3 in order to access the data without authentication
github_header="Accept: application/vnd.github.v3+json" 

boldprint () { printf "|\n| \033[1m${@}\033[0m\n|\n" ; }



SUBSTRATE_PATH=$(pwd)

# Clone the current Polkadot master branch into ./polkadot.
git clone --depth 1 https://gitlab.parity.io/parity/polkadot.git

cd polkadot
# either it's a pull request or the tag/branch exists on github.com
if expr match "${CI_COMMIT_REF_NAME}" '^[0-9]\+$' >/dev/null
then
  boldprint "this is pull request no ${CI_COMMIT_REF_NAME}"
  comppr="$(curl -H "${github_header}" -s ${github_api_polkadot_pull_url}/${CI_COMMIT_REF_NAME} \
    | tr -d '\r\n' | jq -r ".body" \
    | sed -r -n "s;^polkadot companion: paritytech/polkadot#([0-9]+);\1;p;\$\!d")"
  if [ "${comppr}" ]
  then
    boldprint "companion pr found: #${comppr}"
    git fetch origin refs/pull/${comppr}/head:pr/${comppr}
    git checkout pr/${comppr}
  else
    boldprint "no companion pr found - building polkadot:master"
  fi
else
  boldprint "this is not a pull request - building polkadot master"
fi

# Make sure we override the crates in native and wasm build
mkdir .cargo
# echo "paths = [ \"$SUBSTRATE_PATH\" ]" > .cargo/config
# see https://doc.rust-lang.org/cargo/reference/overriding-dependencies.html
echo "[patch.\"https://github.com/paritytech/substrate\"]\nsubstrate = { path = \"$SUBSTRATE_PATH\" }" > .cargo/config
echo ".cargo/config:"
cat .cargo/config
mkdir -p target/debug/wbuild/.cargo
# echo "paths = [ \"$SUBSTRATE_PATH\" ]" > target/debug/wbuild/.cargo/config
cp .cargo/config target/debug/wbuild/.cargo/config

# package, others are updated along the way.
cargo update

# Check whether Polkadot 'master' branch builds with this Substrate commit.
time cargo check


