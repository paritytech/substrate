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


github_api_substrate_pull_url="https://api.github.com/repos/paritytech/substrate/pulls"
# use github api v3 in order to access the data without authentication
github_header="Accept: application/vnd.github.v3+json" 

boldprint () { printf "|\n| \033[1m${@}\033[0m\n|\n" ; }
boldcat () { printf "|\n"; while read l; do printf "| \033[1m${l}\033[0m\n"; done; printf "|\n" ; }



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
if expr match "${CI_COMMIT_REF_NAME}" '^[0-9]\+$' >/dev/null
then
  boldprint "this is pull request no ${CI_COMMIT_REF_NAME}"

  pr_data_file="$(mktemp)"
  # get the last reference to a pr in polkadot
  curl -sSL -H "${github_header}" -o "${pr_data_file}" \
    "${github_api_substrate_pull_url}/${CI_COMMIT_REF_NAME}"

  pr_body="$(sed -n -r 's/^[[:space:]]+"body": (".*")[^"]+$/\1/p' "${pr_data_file}")"

  pr_companion="$(echo "${pr_body}" | sed -n -r \
      -e 's;^.*polkadot companion: paritytech/polkadot#([0-9]+).*$;\1;p' \
      -e 's;^.*polkadot companion: https://github.com/paritytech/polkadot/pull/([0-9]+).*$;\1;p' \
    | tail -n 1)"

  if [ -z "${pr_companion}" ]
  then
    pr_companion="$(echo "${pr_body}" | sed -n -r \
      -e 's;^.*paritytech/polkadot/#([0-9]+).*$;\1;p' \
      -e 's;^.*https://github.com/paritytech/polkadot/pull/([0-9]+).*$;\1;p' \
      | tail -n 1)"
  fi

  if [ "${pr_companion}" ]
  then
    boldprint "companion pr specified/detected: #${pr_companion}"
    git fetch --depth 1 origin refs/pull/${pr_companion}/head:pr/${pr_companion}
    git checkout pr/${pr_companion}
  else
    pr_ref="$(grep -Po '"ref"\s*:\s*"\K(?!master)[^"]*' "${pr_data_file}")"
    if git fetch --depth 1 origin "$pr_ref":branch/"$pr_ref" 2>/dev/null
    then
      boldprint "companion branch detected: $pr_ref"
      git checkout branch/"$pr_ref"
    else
      boldprint "no companion branch found - building polkadot:master"
    fi
  fi
  rm -f "${pr_data_file}"
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

