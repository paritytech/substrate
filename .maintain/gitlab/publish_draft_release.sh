#!/usr/bin/env bash

# shellcheck source=lib.sh
source "$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )/lib.sh"

# Substrate labels for PRs we want to include in the release notes
labels=(
  'B1-runtimenoteworthy'
  'B1-clientnoteworthy'
  'B1-apinoteworthy'
)

version="$CI_COMMIT_TAG"
last_version=$(git tag -l | sort -V | grep -B 1 -x "$version" | head -n 1)
echo "[+] Version: $version; Previous version: $last_version"

# Check that a signed tag exists on github for this version
echo '[+] Checking tag has been signed'
#check_tag "paritytech/substrate" "$version"
case $? in
  0) echo '[+] Tag found and has been signed'
    ;;
  1) echo '[!] Tag found but has not been signed. Aborting release.'; exit 1
    ;;
  2) echo '[!] Tag not found. Aborting release.'; exit
esac

all_changes="$(sanitised_git_logs "$last_version" "$version")"
labelled_changes=""
echo "[+] Iterating through $(wc -l <<< "$all_changes") changes to find labelled PRs"
while IFS= read -r line; do
  pr_id=$(echo "$line" | sed -E 's/.*#([0-9]+)\)$/\1/')

  # Skip if the PR has the silent label - this allows us to skip a few requests
  if has_label 'paritytech/substrate' "$pr_id" 'B0-silent'; then
    continue
  fi
  for label in "${labels[@]}"; do
    if has_label 'paritytech/substrate' "$pr_id" "$label"; then
      labelled_changes="$labelled_changes
$line"
    fi
  done
done <<< "$all_changes"


release_text="Substrate $version
-----------------
$labelled_changes"

echo "[+] Release text generated: "
echo "$release_text"
exit
echo "[+] Pushing release to github"
# Create release on github
release_name="Substrate $version"
data=$(jq -Rs --arg version "$version" \
  --arg release_name "$release_name" \
  --arg release_text "$release_text" \
'{
  "tag_name": $version,
  "target_commitish": "master",
  "name": $release_name,
  "body": $release_text,
  "draft": true,
  "prerelease": false
}' < /dev/null)

out=$(curl -s -X POST --data "$data" -H "Authorization: token $GITHUB_RELEASE_TOKEN" "$api_base/paritytech/substrate/releases")

html_url=$(echo "$out" | jq -r .html_url)

if [ "$html_url" == "null" ]
then
  echo "[!] Something went wrong posting:"
  echo "$out"
else
  echo "[+] Release draft created: $html_url"
fi

echo '[+] Sending draft release URL to Matrix'

msg_body=$(cat <<EOF
**Release pipeline for Substrate $version complete.**
Draft release created: $html_url
EOF
)
formatted_msg_body=$(cat <<EOF
<strong>Release pipeline for Substrate $version complete.</strong><br />
Draft release created: $html_url
EOF
)
send_message "$(structure_message "$msg_body" "$formatted_msg_body")" "$MATRIX_ACCESS_TOKEN"

echo "[+] Done! Maybe the release worked..."
