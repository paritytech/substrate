#!/bin/bash
set -x

TARGET_HOST="$1"
COMMIT=$(echo ${CI_BUILD_REF} | cut -c -9)
DOWNLOAD_URL="https://releases.parity.io/substrate/x86_64-debian:stretch/2.0.0-${COMMIT}/substrate"
POST_DATA='{"extra_vars":{"artifact_path":"'${DOWNLOAD_URL}'","target_host":"'${TARGET_HOST}'"}}'

wget -O - --header "Authorization: Bearer ${AWX_TOKEN}" --header "Content-type: application/json" --post-data "${POST_DATA}" https://ansible-awx.parity.io/api/v2/job_templates/32/launch/
