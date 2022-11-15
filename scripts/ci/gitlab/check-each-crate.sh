#!/usr/bin/env bash

## A script that checks each workspace crate individually.
## It's relevant to check workspace crates individually because otherwise their compilation problems
## due to feature misconfigurations won't be caught, as exemplified by
## https://github.com/paritytech/substrate/issues/12705

set -Eeu -o pipefail
shopt -s inherit_errexit

set -x

target_group="$1"
groups_total="$2"

readarray -t workspace_crates < <(\
  cargo tree --workspace --depth 0 | \
  awk '{ if (length($1) == 0 || substr($1, 1, 1) == "[") { skip } else { print $1 } }'
)

crates_total=${#workspace_crates[*]}
crates_per_group=$(( (crates_total / groups_total) + (crates_total % groups_total > 0) ))

group=1
for ((i=0; i < crates_total; i += crates_per_group)); do
  if [ $group -eq "$target_group" ]; then
    for crate in "${workspace_crates[@]:$i:$crates_per_group}"; do
      cargo check --locked --release -p "$crate"
    done
    break
  fi
  group=$(( group + 1 ))
done
