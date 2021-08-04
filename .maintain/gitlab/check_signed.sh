#!/usr/bin/env bash

# shellcheck source=../common/lib.sh
source "$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )/../common/lib.sh"

version="$CI_COMMIT_TAG"

echo '[+] Checking tag has been signed'
check_tag "paritytech/substrate" "$version"
case $? in
  0) echo '[+] Tag found and has been signed'; exit 0
    ;;
  1) echo '[!] Tag found but has not been signed. Aborting release.'; exit 1
    ;;
  2) echo '[!] Tag not found. Aborting release.'; exit 1
esac
