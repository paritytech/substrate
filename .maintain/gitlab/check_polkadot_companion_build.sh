#!/usr/bin/env bash
#
# check if a pr is compatible with polkadot companion pr or master if not
# available
#
# to override one that was just mentioned mark companion pr in the body of the
# polkadot pr like
#
# polkadot companion: paritytech/polkadot#567
#

set -e

github_api_substrate_pull_url="https://api.github.com/repos/paritytech/substrate/pulls"
# use github api v3 in order to access the data without authentication
github_header="Authorization: token ${GITHUB_PR_TOKEN}"

boldprint () { printf "|\n| \033[1m${@}\033[0m\n|\n" ; }
boldcat () { printf "|\n"; while read l; do printf "| \033[1m${l}\033[0m\n"; done; printf "|\n" ; }



boldcat <<-EOT


check_polkadot_companion_build
==============================

this job checks if there is a string in the description of the pr like

polkadot companion: paritytech/polkadot#567


it will then run cargo check from this polkadot's branch with substrate code
from this pull request. otherwise, it will uses master instead


EOT

# Set the user name and email to make merging work
git config --global user.name 'CI system'
git config --global user.email '<>'

# Merge master into our branch before building Polkadot to make sure we don't miss
# any commits that are required by Polkadot.
git pull origin master

substrate_dir="$PWD"
polkadot_dir="$substrate_dir/polkadot"

git clone --depth 1 https://github.com/paritytech/polkadot.git "$polkadot_dir"

cd "$polkadot_dir"

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
      -e 's;^.*[Cc]ompanion.*paritytech/polkadot#([0-9]+).*$;\1;p' \
      -e 's;^.*[Cc]ompanion.*https://github.com/paritytech/polkadot/pull/([0-9]+).*$;\1;p' \
    | tail -n 1)"

  if [ "${pr_companion}" ]
  then
    boldprint "companion pr specified/detected: #${pr_companion}"
    git fetch origin refs/pull/${pr_companion}/head:pr/${pr_companion}
    git checkout pr/${pr_companion}
    # we want this because `bot merge` will include master into the pr's branch before merging
    git pull origin master
  else
    boldprint "no companion branch found - building polkadot:master"
  fi
  rm -f "${pr_data_file}"
else
  boldprint "this is not a pull request - building polkadot:master"
fi

cd "$substrate_dir"

our_crates=()
our_crates_source="git+https://github.com/paritytech/substrate"
load_our_crates() {
  local found

  while IFS= read -r crate; do
    # for avoiding duplicate entries
    for our_crate in "${our_crates[@]}"; do
      if [ "$crate" == "$our_crate" ]; then
        found=true
        break
      fi
    done
    if [ "${found:-}" ]; then
      unset found
    else
      our_crates+=("$crate")
    fi
  done < <(jq -r '
    . as $in |
    paths |
    select(.[-1]=="source" and . as $p | $in | getpath($p)==null) as $path |
    del($path[-1]) as $path |
    $in | getpath($path + ["name"])
  ' < <(cargo metadata --quiet --format-version=1))
}
load_our_crates

match_their_crates() {
  local target_dir="$1"
  shift

  cd "$target_dir"

  local target_name="$(basename "$target_dir")"
  local crates_not_found=()

  local found

  # output will be provided in the format:
  #   crate
  #   source
  #   crate
  #   ...
  local next="crate"
  while IFS= read -r line; do
    case "$next" in
      crate)
        crate="$line"
        next="source"
      ;;
      source)
        if [ "$line" == "$our_crates_source" ] || [ "$line" == "$our_crates_source?" ]; then
          for our_crate in "${our_crates[@]}"; do
            if [ "$our_crate" == "$crate" ]; then
              found=true
              break
            fi
          done
          if [ "${found:-}" ]; then
            unset found
          else
            # for avoiding duplicate entries
            for crate_not_found in "${crates_not_found[@]}"; do
              if [ "$crate_not_found" == "$crate" ]; then
                found=true
                break
              fi
            done
            if [ "${found:-}" ]; then
              unset found
            else
              crates_not_found+=("$crate")
            fi
          fi
        fi

        next="crate"
      ;;
      *)
        echo "ERROR: Unknown state $next"
        exit 1
      ;;
    esac
  done < <(jq -r '
    . as $in |
    paths(select(type=="string")) |
    select(.[-1]=="source") as $source_path |
    del($source_path[-1]) as $path |
    [$in | getpath($path + ["name"]), getpath($path + ["source"])] |
    .[]
  ' < <(cargo metadata --quiet --format-version=1))

  if [ "$crates_not_found" ]; then
    echo "Errors during crate matching"
    printf "Failed to find crate \"%s\" referenced in $target_name\n" "${crates_not_found[@]}"
    exit 1
  fi
}
match_their_crates "$polkadot_dir"

# Patch all Substrate crates in Polkadot
cd "$polkadot_dir"
diener patch --crates-to-patch "$substrate_dir" --substrate --path Cargo.toml

# Test Polkadot pr or master branch with this Substrate commit.
time cargo test --workspace --release --verbose --features=runtime-benchmarks
