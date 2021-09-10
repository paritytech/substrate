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

set -eu -o pipefail
shopt -s inherit_errexit

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
git config --global pull.rebase false

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

our_crates=()
our_crates_source="git+https://github.com/paritytech/substrate"
discover_our_crates() {
  local found

  cd "$substrate_dir"

  # workaround for early exits not being detected in command substitution
  # https://unix.stackexchange.com/questions/541969/nested-command-substitution-does-not-stop-a-script-on-a-failure-even-if-e-and-s
  local last_line
  while IFS= read -r crate; do
    last_line="$crate"
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
  # dependencies with {"source": null} are the ones we own, hence the getpath($p)==null in the jq
  # script below
  done < <(cargo metadata --quiet --format-version=1 | jq -r '
    . as $in |
    paths |
    select(.[-1]=="source" and . as $p | $in | getpath($p)==null) as $path |
    del($path[-1]) as $path |
    $in | getpath($path + ["name"])
  ')
  if [ -z "${last_line+_}" ]; then
    echo "No lines were read for cargo metadata of $PWD (some error probably occurred)"
    exit 1
  fi
}
discover_our_crates

match_their_crates() {
  local target_dir="$1"
  shift

  cd "$target_dir"

  local target_name="$(basename "$target_dir")"
  local crates_not_found=()
  local found

  # workaround for early exits not being detected in command substitution
  # https://unix.stackexchange.com/questions/541969/nested-command-substitution-does-not-stop-a-script-on-a-failure-even-if-e-and-s
  local last_line
  # output will be consumed in the format:
  #   crate
  #   source
  #   crate
  #   ...
  local next="crate"
  while IFS= read -r line; do
    last_line="$line"
    case "$next" in
      crate)
        next="source"
        crate="$line"
      ;;
      source)
        next="crate"
        if [ "$line" == "$our_crates_source" ] || [[ "$line" == "$our_crates_source?"* ]]; then
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
      ;;
      *)
        echo "ERROR: Unknown state $next"
        exit 1
      ;;
    esac
  done < <(cargo metadata --quiet --format-version=1 | jq -r '
    . as $in |
    paths(select(type=="string")) |
    select(.[-1]=="source") as $source_path |
    del($source_path[-1]) as $path |
    [$in | getpath($path + ["name"]), getpath($path + ["source"])] |
    .[]
  ')
  if [ -z "${last_line+_}" ]; then
    echo "No lines were read for cargo metadata of $PWD (some error probably occurred)"
    exit 1
  fi

  if [ "${crates_not_found[@]}" ]; then
    echo -e "Errors during crate matching\n"
    printf "Failed to detect our crate \"%s\" referenced in $target_name\n" "${crates_not_found[@]}"
    echo -e "Note: this error generally happens if you have deleted or renamed a crate and did not update it in $target_name. Consider opening a companion pull request on $target_name and referencing it in this pull request's description like:\n$target_name companion: [your companion PR here]"
    exit 1
  fi
}
match_their_crates "$polkadot_dir"

# Patch all Substrate crates in Polkadot
cd "$polkadot_dir"
diener patch --crates-to-patch "$substrate_dir" --substrate --path Cargo.toml

# Test Polkadot pr or master branch with this Substrate commit.
time cargo test --workspace --release --verbose --features=runtime-benchmarks
