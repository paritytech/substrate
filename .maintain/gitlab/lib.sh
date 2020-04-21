#!/bin/sh

api_base="https://api.github.com/repos"

# Function to take 2 git tags/commits and get any lines from commit messages
# that contain something that looks like a PR reference: e.g., (#1234)
sanitised_git_logs(){
  git --no-pager log --pretty=format:"%s" "$1..$2" |
  # Only find messages referencing a PR
  grep -E '\(#[0-9]+\)' |
  # Strip any asterisks
  sed 's/^* //g' |
  # And add them all back
  sed 's/^/* /g'
}

# Returns the last published release on github
# Note: we can't just use /latest because that ignores prereleases
# repo: 'organization/repo'
# Usage: last_github_release "$repo"
last_github_release(){
  i=0
  # Iterate over releases until we find the last release that's not just a draft
  while [ $i -lt 29 ]; do
    out=$(curl -H "Authorization: token $GITHUB_RELEASE_TOKEN" -s "$api_base/$1/releases" | jq ".[$i]")
    echo "$out"
    # Ugh when echoing to jq, we need to translate newlines into spaces :/
    if [ "$(echo "$out" | tr '\r\n' ' ' | jq '.draft')" = "false" ]; then
      echo "$out" | tr '\r\n' ' ' | jq '.tag_name'
      return
    else
      i=$((i + 1))
    fi
  done
}

# Checks whether a tag on github has been verified
# repo: 'organization/repo'
# tagver: 'v1.2.3'
# Usage: check_tag $repo $tagver
check_tag () {
  repo=$1
  tagver=$2
  tag_out=$(curl -H "Authorization: token $GITHUB_RELEASE_TOKEN" -s "$api_base/$repo/git/refs/tags/$tagver")
  tag_sha=$(echo "$tag_out" | jq -r .object.sha)
  object_url=$(echo "$tag_out" | jq -r .object.url)
  if [ "$tag_sha" = "null" ]; then
    return 2
  fi
  verified_str=$(curl -H "Authorization: token $GITHUB_RELEASE_TOKEN" -s "$object_url" | jq -r .verification.verified)
  if [ "$verified_str" = "true" ]; then
    # Verified, everything is good
    return 0
  else
    # Not verified. Bad juju.
    return 1
  fi
}

# Checks whether a given PR has a given label.
# repo: 'organization/repo'
# pr_id: 12345
# label: B1-silent
# Usage: has_label $repo $pr_id $label
has_label(){
  repo="$1"
  pr_id="$2"
  label="$3"
  out=$(curl -H "Authorization: token $GITHUB_RELEASE_TOKEN" -s "$api_base/$repo/pulls/$pr_id")
  [ -n "$(echo "$out" | jq ".labels | .[] | select(.name==\"$label\")")" ]
}

# Formats a message into a JSON string for posting to Matrix
# message: 'any plaintext message'
# formatted_message: '<strong>optional message formatted in <em>html</em></strong>' 
# Usage: structure_message $content $formatted_content (optional)
structure_message() {
  if [ -z "$2" ]; then
    body=$(jq -Rs --arg body "$1" '{"msgtype": "m.text", $body}' < /dev/null)
  else
    body=$(jq -Rs --arg body "$1" --arg formatted_body "$2" '{"msgtype": "m.text", $body, "format": "org.matrix.custom.html", $formatted_body}' < /dev/null)
  fi
  echo "$body"
}

# Post a message to a matrix room
# body: '{body: "JSON string produced by structure_message"}'
# room_id: !fsfSRjgjBWEWffws:matrix.parity.io
# access_token: see https://matrix.org/docs/guides/client-server-api/
# Usage: send_message $body (json formatted) $room_id $access_token
send_message() {
curl -XPOST -d "$1" "https://matrix.parity.io/_matrix/client/r0/rooms/$2/send/m.room.message?access_token=$3"
}


# highlight output in gitlab job logs
boldprint () { printf "|\n| \033[1m${@}\033[0m\n|\n" ; }
boldcat () { printf "|\n"; while read l; do printf "| \033[1m${l}\033[0m\n"; done; printf "|\n" ; }


# find polkadot companion pr
# either do this on the description of the current pull request or figure out 
# the master branches last pull request and start from there
# substrate pr no: 1234
# prnonly: optional -- return pr no only
companion_pr() {

  prno="${1}"

  print_ref () {
    if [ "${2}" = "prnonly" ]
    then
      print "${1}"
    else
      print "pull/${1}/head"
    fi
  }

 
  github_api_substrate_pull_url="${api_base}/paritytech/substrate/pulls"
  # use github api v3 in order to access the data without authentication
  github_header="Accept: application/vnd.github.v3+json" 


  pr_data_file="$(mktemp)"
  # get the last reference to a pr in polkadot
  curl -sSL -H "${github_header}" -o "${pr_data_file}" \
    "${github_api_substrate_pull_url}/${prno}"

  pr_body="$(sed -n -r 's/^[[:space:]]+"body": (".*")[^"]+$/\1/p' "${pr_data_file}")"
  pr_ref="$(grep -Po '"ref"\s*:\s*"\K(?!master)[^"]*' "${pr_data_file}")"
  rm -f "${pr_data_file}"

  # check for explicit statement first
  companion="$(echo "${pr_body}" | sed -n -r \
      -e 's;^.*polkadot companion: paritytech/polkadot#([0-9]+).*$;\1;p' \
      -e 's;^.*polkadot companion: https://github.com/paritytech/polkadot/pull/([0-9]+).*$;\1;p' \
    | tail -n 1)"


  test "${companion}" && print_ref "${companion}" "${2}" && return


  # then check for polkadot pr mentionings
  companion="$(echo "${pr_body}" | sed -n -r \
    -e 's;^.*paritytech/polkadot/#([0-9]+).*$;\1;p' \
    -e 's;^.*https://github.com/paritytech/polkadot/pull/([0-9]+).*$;\1;p' \
    | tail -n 1)"

  test "${companion}" && print_ref "${companion}" "${2}" && return
  test "${2}" = "prnonly" && return 1

  # last resort check if there is a polkadot pr with the same branch name
  if curl -sSL -H "${github_header}" \
    "${api_base}/paritytech/polkadot/git/ref/heads/${pr_ref}" \
    | grep -q "\"refs/heads/${pr_ref}\""

    print "heads/${pr_ref}"
  fi
}


# check the status of a pull request - needs to be
# mergable and approved
# polkadot companion pr no: 1234
check_mergeability() {
  
  github_api_polkadot_pull_url="${api_base}/paritytech/polkadot/pulls"
  # use github api v3 in order to access the data without authentication
  github_header="Accept: application/vnd.github.v3+json" 

  companion="${1}"
  

  curl -H "${github_header}" -sS -o companion_pr.json \
    ${github_api_polkadot_pull_url}/${companion} 
  
  if jq -e .merged < companion_pr.json >/dev/null
  then
    boldprint "polkadot pr #${companion} already merged"
    return 0
  fi
  
  if jq -e '.mergeable' < companion_pr.json >/dev/null
  then
    boldprint "polkadot pr #${companion} mergeable"
  else
    boldprint "polkadot pr #${companion} not mergeable"
    return 1
  fi
  
  curl -H "${github_header}" -sS -o companion_pr_reviews.json \
    ${github_api_polkadot_pull_url}/${companion}/reviews 
  
  if [ -n "$(jq -r -e '.[].state | select(. == "CHANGES_REQUESTED")' < companion_pr_reviews.json)" ] && \
    [ -z "$(jq -r -e '.[].state | select(. == "APPROVED")' < companion_pr_reviews.json)" ]
  then
    boldprint "polkadot pr #${companion} not APPROVED"
    return 1
  fi
  
  boldprint "polkadot pr #${pr_companion} state APPROVED"
  return 0
}
