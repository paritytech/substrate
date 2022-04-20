#!/usr/bin/env bash
# set -x

# This script manages the deployment of Substrate rustdocs to https://paritytech.github.io/substrate/.
# - With `deploy` sub-command, it will checkout the passed-in branch/tag ref, build the rustdocs
#   locally (this takes some time), update the `index.html` index page, and push it to remote
#   `gh-pages` branch. So users running this command need to have write access to the remote
#   `gh-pages` branch. This sub-command depends on [@substrate/index-tpl-crud](https://www.npmjs.com/package/@substrate/index-tpl-crud)
#   to update the DOM of index.html page.
# - With `remove` sub-command, it will remove the deployed rustdocs from `gh-pages`, and update the
#   index.html page as necessary. It may remove the `latest` symbolic link.
#
# Examples:
#   # Showing help text
#   rustdocs-release.sh -h
#
#   # Deploy rustdocs of `monthly-2021-10` tag
#   rustdocs-release.sh deploy monthly-2021-10
#
#   # In addition to the above, the `latest` symlink will point to this version of rustdocs
#   rustdocs-release.sh deploy -l monthly-2021-10
#
#   # Remove the rustdocs of `monthly-2021-10` from `gh-pages`.
#   rustdocs-release.sh remove monthly-2021-10
#
# Dependencies:
#   - @substrate/index-tpl-crud - https://www.npmjs.com/package/@substrate/index-tpl-crud
#

# Script setting
# The git repo http URL
REMOTE_REPO="https://github.com/paritytech/substrate.git"
TMP_PREFIX="/tmp"                             # tmp location that the built doc is copied to.
DOC_INDEX_PAGE="sc_service/index.html"

# Set to `true` if using cargo `nightly` toolchain to build the doc.
# Set to `false` to use the default cargo toolchain. This is preferred if you want to build
# the rustdocs with a pinned nightly version set to your default toolchain.
CARGO_NIGHTLY=false

# Set the git remote name. Most of the time the default is `origin`.
GIT_REMOTE="origin"
LATEST=false

# Setting the help text
declare -A HELP_TXT
HELP_TXT["deploy"]=$(cat <<-EOH
Build and deploy the rustdocs of the specified branch/tag to \`gh-pages\` branch.

  usage:      $0 deploy [-l] <git_branch_ref>
  example:    $0 deploy -l monthly-2021-10

  options:
    -l        The \`latest\` path will be sym'linked to this rustdocs version
EOH
)

HELP_TXT["remove"]=$(cat <<-EOH
Remove the rustdocs of the specified version from \`gh-pages\` branch.

  usage:      $0 remove <git_branch_ref>
  example:    $0 remove monthly-2021-10
EOH
)

set_and_check_rustdoc_ref() {
  [[ -z "$1" ]] && {
    echo -e "git branch_ref is not specified.\n"
    echo "${HELP_TXT[$2]}"
    exit 1
  }
  BUILD_RUSTDOC_REF=$1
}

check_local_change() {
  # Check there is no local changes before proceeding
  [[ -n $(git status --porcelain) ]] \
    && echo "Local changes exist, please either discard or commit them as this command will change the current checkout branch." \
    && exit 1
}

build_rustdocs() {
  # Build the docs
  time cargo $($CARGO_NIGHTLY && echo "+nightly") doc --workspace --all-features --verbose \
    || { echo "Generate $1 rustdocs failed" && exit 1; }
  rm -f target/doc/.lock

  # Moving the built doc to the tmp location
  mv target/doc "${2}"
  [[ -n "${DOC_INDEX_PAGE}" ]] \
    && echo "<meta http-equiv=refresh content=0;url=${DOC_INDEX_PAGE}>" > "${2}/index.html"
}

upsert_index_page() {
  # Check if `index-tpl-crud` exists
  which index-tpl-crud &> /dev/null || yarn global add @substrate/index-tpl-crud
  index-tpl-crud upsert $($1 && echo "-l") ./index.html "$2"
}

rm_index_page() {
  which index-tpl-crud &> /dev/null || yarn global add @substrate/index-tpl-crud
  index-tpl-crud rm ./index.html "$1"
}

git_add_commit_push() {
  git add --all
  git commit -m "$1" || echo "Nothing to commit"
  git push "${GIT_REMOTE}" gh-pages --force
}

import_gh_key() {
  [[ -n $GITHUB_SSH_PRIV_KEY ]] && {
    eval $(ssh-agent)
    ssh-add - <<< $GITHUB_SSH_PRIV_KEY
  }

  # Adding github.com as known_hosts
  ssh-keygen -F github.com &>/dev/null || {
    [[ -e ~/.ssh ]] || mkdir ~/.ssh
    [[ -e ~/.ssh/known_hosts ]] || touch ~/.ssh/known_hosts
    ssh-keyscan -t rsa github.com >> ~/.ssh/known_hosts
  }
}

deploy_main() {
  check_local_change
  import_gh_key

  CURRENT_GIT_BRANCH=$(git rev-parse --abbrev-ref HEAD)
  TMP_PROJECT_PATH="${TMP_PREFIX}/${PROJECT_NAME}"
  DOC_PATH="${TMP_PROJECT_PATH}/${BUILD_RUSTDOC_REF}"

  # Build the tmp project path
  rm -rf "${TMP_PROJECT_PATH}" && mkdir "${TMP_PROJECT_PATH}"

  # Copy .gitignore file to tmp
  [[ -e "${PROJECT_PATH}/.gitignore" ]] && cp "${PROJECT_PATH}/.gitignore" "${TMP_PROJECT_PATH}"

  git fetch --all
  git checkout -f ${BUILD_RUSTDOC_REF} || { echo "Checkout \`${BUILD_RUSTDOC_REF}\` error." && exit 1; }
  build_rustdocs "${BUILD_RUSTDOC_REF}" "${DOC_PATH}"

  # git checkout `gh-pages` branch
  git fetch "${GIT_REMOTE}" gh-pages
  git checkout gh-pages
  # Move the built back
  [[ -e "${TMP_PROJECT_PATH}/.gitignore" ]] && cp -f "${TMP_PROJECT_PATH}/.gitignore" .
  # Ensure the destination dir doesn't exist under current path.
  rm -rf "${BUILD_RUSTDOC_REF}"
  mv -f "${DOC_PATH}" "${BUILD_RUSTDOC_REF}"

  upsert_index_page $LATEST "${BUILD_RUSTDOC_REF}"
  # Add the latest symlink
  $LATEST && rm -rf latest && ln -sf "${BUILD_RUSTDOC_REF}" latest

  git_add_commit_push "___Deployed rustdocs of ${BUILD_RUSTDOC_REF}___"
  # Clean up
  # Remove the tmp asset created
  rm -rf "${TMP_PROJECT_PATH}"
  # Resume back previous checkout branch.
  git checkout -f "$CURRENT_GIT_BRANCH"
}

remove_main() {
  check_local_change
  import_gh_key

  CURRENT_GIT_BRANCH=$(git rev-parse --abbrev-ref HEAD)

  # git checkout `gh-pages` branch
  git fetch "${GIT_REMOTE}" gh-pages
  git checkout gh-pages

  rm -rf "${BUILD_RUSTDOC_REF}"
  rm_index_page "${BUILD_RUSTDOC_REF}"
  # check if the destination of `latest` exists and rmove if not.
  [[ -e "latest" ]] || rm latest

  git_add_commit_push "___Removed rustdocs of ${BUILD_RUSTDOC_REF}___"

  # Resume back previous checkout branch.
  git checkout -f "$CURRENT_GIT_BRANCH"
}

# ---- The script execution entry point starts here ----

# Arguments handling
SUBCMD=$1
[[ $SUBCMD == "deploy" || $SUBCMD == "remove" ]] \
  || { echo "Please specify a subcommand of \`deploy\` or \`remove\`" && exit 1 ;}
shift

# After removing the subcommand, there could only be 1 or 2 parameters afterward
[[ $# -lt 1 || $# -gt 2 ]] && {
  echo "${HELP_TXT[${SUBCMD}]}"
  exit 1
}

# Parsing options and argument for `deploy` subcommand
[[ $SUBCMD == "deploy" ]] && {
  while getopts :lh opt; do
    case $opt in
      l)
        LATEST=true
        ;;
      h)
        echo "${HELP_TXT[$SUBCMD]}"
        exit 0
        ;;
      \?)
        echo "Invalid option: -$OPTARG" >&2
        exit 1
        ;;
    esac
  done
}
# Parsing options and argument for `remove` subcommand
[[ $SUBCMD == "remove" ]] && {
  while getopts :h opt; do
    case $opt in
      h)
        echo "${HELP_TXT[$SUBCMD]}"
        exit 0
        ;;
      \?)
        echo "Invalid option: -$OPTARG" >&2
        exit 1
        ;;
    esac
  done
}

shift $(($OPTIND - 1))
set_and_check_rustdoc_ref ${1:-''} $SUBCMD

SCRIPT=$(realpath $0)
SCRIPT_PATH=$(dirname $SCRIPT)
PROJECT_PATH=$(dirname ${SCRIPT_PATH})
PROJECT_NAME=$(basename "$PROJECT_PATH")

pushd "${PROJECT_PATH}" &>/dev/null
[[ $SUBCMD == "deploy" ]] && deploy_main
[[ $SUBCMD == "remove" ]] && remove_main
popd &>/dev/null
