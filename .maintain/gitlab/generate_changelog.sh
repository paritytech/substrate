#!/usr/bin/env bash

# shellcheck source=../common/lib.sh
source "$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )/../common/lib.sh"

version="$2"
last_version="$1"

all_changes="$(sanitised_git_logs "$last_version" "$version")"
runtime_changes=""
api_changes=""
client_changes=""
changes=""
migrations=""

while IFS= read -r line; do
  pr_id=$(echo "$line" | sed -E 's/.*#([0-9]+)\)$/\1/')

  # Skip if the PR has the silent label - this allows us to skip a few requests
  if has_label 'paritytech/substrate' "$pr_id" 'B0-silent'; then
    continue
  fi
  if has_label 'paritytech/substrate' "$pr_id" 'B3-apinoteworthy' ; then
    api_changes="$api_changes
$line"
  fi
  if has_label 'paritytech/substrate' "$pr_id" 'B5-clientnoteworthy'; then
    client_changes="$client_changes
$line"
  fi
  if has_label 'paritytech/substrate' "$pr_id" 'B7-runtimenoteworthy'; then
    runtime_changes="$runtime_changes
$line"
  fi
  if has_label 'paritytech/substrate' "$pr_id" 'E1-runtime-migration'; then
    migrations="$migrations
$line"
  fi
done <<< "$all_changes"

# Make the substrate section if there are any substrate changes
if [ -n "$runtime_changes" ] ||
   [ -n "$api_changes" ] ||
   [ -n "$client_changes" ] ||
   [ -n "$migrations" ]; then
  changes=$(cat << EOF
Substrate changes
-----------------

EOF
)
  if [ -n "$runtime_changes" ]; then
    changes="$changes

Runtime
-------
$runtime_changes"
  fi
  if [ -n "$client_changes" ]; then
    changes="$changes

Client
------
$client_changes"
  fi
  if [ -n "$api_changes" ]; then
    changes="$changes

API
---
$api_changes"
  fi
  release_text="$release_text

$changes"
fi
if [ -n "$migrations" ]; then
  changes="$changes

Runtime Migrations
------------------
$migrations"
fi

echo "$changes"
