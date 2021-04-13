#!/bin/bash

set -eu
# API trigger another project's pipeline
curl --silent \
    -X POST \
    -F "token=${CI_JOB_TOKEN}" \
    -F "ref=master" \
    -F "variables[TRGR_PROJECT]=${TRGR_PROJECT}" \
    -F "variables[TRGR_REF]=${TRGR_REF}" \
    -F "variables[IMAGE_NAME]=${IMAGE_NAME}" \
    -F "variables[IMAGE_TAG]=${IMAGE_TAG}" \
    "https://${CI_SERVER_HOST}/api/v4/projects/${DWNSTRM_ID}/trigger/pipeline" | \
        tee pipeline

PIPELINE_ID=$(cat pipeline | jq ".id")
echo "\nWaiting on ${PIPELINE_ID} status..."

# This part polls for the triggered pipeline status, the native
# `trigger` job does not return this status via API.
# This is a workaround for a Gitlab bug, waits here until
# https://gitlab.com/gitlab-org/gitlab/-/issues/326137 gets fixed.
# The timeout is 360 curls with 8 sec interval, roughly an hour.

function get_status() {
    curl --silent \
        --header "PRIVATE-TOKEN: ${PIPELINE_TOKEN}" \
        "https://${CI_SERVER_HOST}/api/v4/projects/${DWNSTRM_ID}/pipelines/${PIPELINE_ID}" | \
            jq --raw-output ".status";
}

for i in $(seq 1 360); do
    STATUS=$(get_status);
    echo "Triggered pipeline status is ${STATUS}";
    if [[ ${STATUS} =~ ^(pending|running|created)$ ]]; then
        echo "Busy...";
    elif [[ ${STATUS} =~ ^(failed|canceled|skipped|manual)$ ]]; then
        exit 1;
    elif [[ ${STATUS} =~ ^(success)$ ]]; then
        exit 0;
    else
        exit 1;
    fi
sleep 8;
done
