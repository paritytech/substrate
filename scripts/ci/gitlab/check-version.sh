#!/bin/bash

VERSION_SHA="$(cat ./artifacts/substrate/VERSION | cut -f 3 -d'-' )"

echo CI_COMMIT_SHA: ${CI_COMMIT_SHA}
echo VERSION_SHA: ${VERSION_SHA}
if [[ ${CI_COMMIT_SHA} == ${VERSION_SHA}* ]]; then
  exit 0
fi

exit 1
