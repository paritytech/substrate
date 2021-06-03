#!/usr/bin/env sh
#
# check if a pr is compatible with companion pr or master if not available
#
# to override one that was just mentioned mark companion pr in the body of the
# pr like
#
# $REPO companion: $ORGANISATION/$REPO#567
#
# $ORGANISATION and $REPO are set using $1 and $2
# So invoke this script like:
# ./check_companion_build.sh paritytech polkadot

set -e

ORGANISATION=$1
REPO=$2


github_api_substrate_pull_url="https://api.github.com/repos/paritytech/substrate/pulls"
# use github api v3 in order to access the data without authentication
github_header="Authorization: token ${GITHUB_PR_TOKEN}"

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

  pr_data_file="$(mktemp)"
  # get the last reference to a pr in the target repo
  curl -sSL -H "${github_header}" -o "${pr_data_file}" \
    "${github_api_substrate_pull_url}/${CI_COMMIT_REF_NAME}"

  pr_body="$(sed -n -r 's/^[[:space:]]+"body": (".*")[^"]+$/\1/p' "${pr_data_file}")"

  pr_companion="$(echo "${pr_body}" | sed -n -r \
      -e "s;^.*[Cc]ompanion.*${ORGANISATION}/${REPO}#([0-9]+).*$;\1;p" \
      -e "s;^.*[Cc]ompanion.*https://github.com/${ORGANISATION}/${REPO}/pull/([0-9]+).*$;\1;p" \
    | tail -n 1)"

  if [ "${pr_companion}" ]
  then
    boldprint "companion pr specified/detected: #${pr_companion}"
    git fetch origin refs/pull/${pr_companion}/head:pr/${pr_companion}
    git checkout pr/${pr_companion}
    git merge origin/master
  else
    boldprint "no companion branch found - building ${REPO}:master"
  fi
  rm -f "${pr_data_file}"
else
  boldprint "this is not a pull request - building ${REPO}:master"
fi

# Patch all Substrate crates in the repo
diener patch --crates-to-patch ../ --substrate --path Cargo.toml

# Test pr or master branch with this Substrate commit.
time cargo test --all --release --verbose
