#!/usr/bin/env bash

# 1. checkout the certain branch / tag
# 2. Run `cargo build to build the docs`
# 3. copy the doc folder over to `/tmp`
# 4. Now, you need to switch your substrate folder branch to gh-page
#    - copy the doc folder to this folder,
#    - if `latest` flag is added, update the `index.html`
#    - git force push back to the substrate git repo

# Example:
#   rustdocs-release.sh --help
#   rustdocs-release.sh deploy monthly-2021-12
#   rustdocs-release.sh deploy --latest monthly-2021-12
#   rustdocs-release.sh remove monthly-2021-12


REMOTE_REPO="https://github.com/paritytech/substrate.git"


# 1. checkout the certain branch / tag
# Assuming we check out from the Substrate repo
SCRIPT=`realpath $0`
SCRIPT_PATH=`dirname $SCRIPT`
pushd "${SCRIPT_PATH}/.."

BRANCH_TAG=$1
git checkout $BRANCH_TAG


popd
