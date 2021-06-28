#!/usr/bin/env bash
#
# check if a pr is compatible with companion pr or master if not available
#
# to override one that was just mentioned mark companion pr in the body of the
# pr like
#
# $REPO companion: $ORGANISATION/$REPO#567
#
# $ORGANISATION and $REPO are set using $1 and $2. You can also specify a custom
# build command with $3
# So invoke this script like:
# ./check_companion_build.sh paritytech polkadot 'cargo test --release'

set -e

# Include the common functions library
#shellcheck source=../common/lib.sh
. "$(dirname "${0}")/../common/lib.sh"

ORGANISATION=$1
REPO=$2
BUILDSTRING=${3:-cargo test --workspace --release}
DEPS=("${@:4}")

boldprint () { printf "|\n| \033[1m%s\033[0m\n|\n" "${@}"; }
boldcat () { printf "|\n"; while read -r l; do printf "| \033[1m%s\033[0m\n" "${l}"; done; printf "|\n" ; }

boldcat <<-EOT


check_${REPO}_companion_build
==============================

this job checks if there is a string in the description of the pr like

$REPO companion: $ORGANISATION/$REPO#567


it will then run cargo check from this ${REPO}'s branch with substrate code
from this pull request. otherwise, it will uses master instead


EOT

# Set the user name and email to make merging work
git config --global user.name 'CI system'
git config --global user.email '<>'

# Merge master into our branch before building to make sure we don't miss
# any commits that are required.
git fetch --depth 100 origin
git merge origin/master

# Clone the current master branch into a local directory
# NOTE: we need to pull enough commits to be able to find a common
# ancestor for successfully performing merges below.
git clone --depth 20 "https://github.com/${ORGANISATION}/${REPO}.git"

cd "$REPO"

# either it's a pull request then check for a companion otherwise use
# master
# shellcheck disable=SC2003
if expr match "${CI_COMMIT_REF_NAME}" '^[0-9]\+$' >/dev/null
then
  boldprint "this is pull request no ${CI_COMMIT_REF_NAME}"
  pr_companion="$(get_companion "paritytech/substrate" "$CI_COMMIT_REF_NAME" "$ORGANISATION/$REPO")"
  if [ "$pr_companion" ]
  then
    boldprint "companion pr specified/detected: #${pr_companion}"
    git fetch origin "refs/pull/${pr_companion}/head:pr/${pr_companion}"
    git checkout "pr/${pr_companion}"
    git merge origin/master
  else
    boldprint "no companion branch found - building ${REPO}:master"
  fi

  # If this repo has any additional dependencies, we should check whether they
  # are mentioned as companions as well, and patch to use that if so
  # Note: Will only work with repos supported by diener
  declare -A diener_commands
  diener_commands=()
  diener_commands["paritytech/polkadot"]='--polkadot'
  diener_commands["paritytech/substrate"]='--substrate'
  diener_commands["paritytech/grandpa-bridge-gadget"]='--beefy'

  for dep in "${DEPS[@]}"; do
    dep_companion="$(get_companion "paritytech/substrate" "$CI_COMMIT_REF_NAME" "$dep")"
    if [ "$dep_companion" ]; then
      echo "Companion PR found for $dep, need to patch $REPO to use that"
      git clone --depth 20 "https://github.com/$dep.git" "$dep"
      git -C "$dep" fetch origin "refs/pull/${dep_companion}/head:pr/${dep_companion}"
      git -C "$dep" checkout "pr/${dep_companion}"
      git -C "$dep" merge origin/master
      diener patch --crates-to-patch "$dep" "${diener_commands[$dep]}" --path "Cargo.toml"
    fi

  done

else
  boldprint "this is not a pull request - building ${REPO}:master"
fi


# Patch polkadot, substrate or beefy deps as required
declare -A match_arg
match_arg=()
match_arg["--substrate"]='source = "git+https://github.com/paritytech/substrate?'
match_arg["--polkadot"]='source = "git+https://github.com/paritytech/polkadot?'
match_arg["--beefy"]='source = "git+https://github.com/paritytech/parity-bridges-gadget?'

declare -A patch_args
patch_args=()

# For each Cargo.lock
while IFS= read -r cargo_lock; do
  # If the Cargo.lock has a dependency, we patch with diener
  for patch_arg in "${!match_arg[@]}"; do
    if grep -q "${match_arg[$patch_arg]}" "$cargo_lock" ; then
      echo "marking $patch_arg as patchable"
      patch_args["$patch_arg"]='true'
      echo "patching $patch_arg"
    fi
  done
done < <(find . -name Cargo.lock)

for patch_arg in "${!patch_args[@]}"; do
  echo "patching $patch_arg"
  diener patch --crates-to-patch ../ "$patch_arg" --path Cargo.toml
done

# Test pr or master branch with this Substrate commit.
eval "$BUILDSTRING"
