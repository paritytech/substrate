#!/bin/sh
url="https://github.com/paritytech/substrate/${CI_COMMIT_REF_NAME}"
echo "[+] API URL: $url"

draft_state=$(curl "$url" | jq -r .draft)
echo "[+] Draft state: $draft_state"

if [ "$draft_state" = 'true' ]; then
  echo "[!] PR is currently a draft, stopping pipeline"
  exit 1
else
  echo "[+] PR is not a draft. Proceeding with CI pipeline"
  exit 0
fi
