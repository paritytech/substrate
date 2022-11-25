#!/usr/bin/env bash

## A script that checks each workspace crate individually.
## It's relevant to check workspace crates individually because otherwise their compilation problems
## due to feature misconfigurations won't be caught, as exemplified by
## https://github.com/paritytech/substrate/issues/12705

set -Eeu -o pipefail
shopt -s inherit_errexit

set -vx

target_group="$1"
groups_total="$2"

readarray -t workspace_crates < <(\
  cargo tree --workspace --depth 0 --prefix none |
  awk '{ if (length($1) == 0 || substr($1, 1, 1) == "[") { skip } else { print $1 } }' |
  sort |
  uniq
)

crates_total=${#workspace_crates[*]}
if [ "$crates_total" -lt 1 ]; then
  >&2 echo "No crates detected for $PWD"
  exit 1
fi

if [ "$crates_total" -lt "$groups_total" ]; then
  # `crates_total / groups_total` would result in 0, so round it up to 1
  crates_per_group=1
else
  # We add `crates_total % groups_total > 0` (which evaluates to 1 in case there's a remainder for
  # `crates_total % groups_total`) to round UP `crates_total / groups_total` 's
  # potentially-fractional result to the nearest integer. Doing that ensures that we'll not miss any
  # crate in case `crates_total / groups_total` would normally result in a fractional number, since
  # in those cases Bash would round DOWN the result to the nearest integer. For example, if
  # `crates_total = 5` and `groups_total = 2`, then `crates_total / groups_total` would round down
  # to 2; since the loop below would then step by 2, we'd miss the 5th crate.
  crates_per_group=$(( (crates_total / groups_total) + (crates_total % groups_total > 0) ))
fi

group=1
for ((i=0; i < crates_total; i += crates_per_group)); do
  if [ $group -eq "$target_group" ]; then
    crates_in_group=("${workspace_crates[@]:$i:$crates_per_group}")
    echo "crates in the group: ${crates_in_group[*]}" >/dev/null # >/dev/null due to "set -x"
    for crate in "${crates_in_group[@]}"; do
      cargo check --locked --release -p "$crate"
    done
    break
  fi
  group=$(( group + 1 ))
done
