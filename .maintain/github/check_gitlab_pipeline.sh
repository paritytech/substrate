#!/bin/bash
SUBSTRATE_API_BASEURL="https://gitlab.parity.io/api/v4/projects/145"

TAG_NAME=$(echo "$GITHUB_REF" | sed -E 's_refs/tags/(.*)_\1_')
PIPELINE_ID=$(curl -s $SUBSTRATE_API_BASEURL/pipelines | jq -r "map(select(.ref==\"$TAG_NAME\")) | .[0] | .id")
if [ "$PIPELINE_ID" == "null" ]; then
  echo "[!] Pipeline for $TAG_NAME not found. Exiting."
  exit 1
fi

echo "[+] Pipeline path: https://gitlab.parity.io/parity/substrate/pipelines/$PIPELINE_ID"

# 130 minute job max
for (( c=0; c < 180; c++ )); do
  out=$(curl -s "$SUBSTRATE_API_BASEURL/pipelines/$PIPELINE_ID" | jq -r .status)
  case $out in
    "success")
      echo "[+] Pipeline $PIPELINE_ID for $TAG_NAME succeeded!"
      exit 0
      ;;
    "failed")
      echo "[!] Pipeline $PIPELINE_ID for $TAG_NAME failed. Cannot proceed. Check job output on gitlab!"
      exit 1
      ;;
    "cancelled")
      echo "[!] Pipeline $PIPELINE_ID for $TAG_NAME was cancelled. Cannot proceed!"
      exit 1
      ;;
    "running")
      echo "[-] Pipeline $PIPELINE_ID for $TAG_NAME still in progress..."
  esac
  sleep 60
done
# If we reach here, we timed out after 30 minutes
echo "[!] Pipeline $PIPELINE_ID for $TAG_NAME timed out! Cannot proceed"
echo "::set-output name=pipeline_status::timedout"
exit 1
