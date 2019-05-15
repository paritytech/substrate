#!/bin/bash
set -x

export download_url="https://releases.parity.io/substrate/x86_64-debian:stretch/2.0.0-${CI_COMMIT_SHORT_SHA}/substrate"

wget -O -  --header "Authorization: Bearer ${AWX_TOKEN}" --header "Content-type: application/json" --post-data '{"extra_vars":{"artifact_path":"${download_url}"}' https://ansible-awx.parity.io/api/v2/job_templates/32/launch/


