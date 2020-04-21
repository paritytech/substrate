#!/bin/sh
#
# check for a polkadot companion pr and ensure it has approvals and is 
# mergeable
#

. $(dirname $0)/lib.sh



boldcat <<-EOT


check_polkadot_companion_status
===============================

this job checks if there is a string in the description of the pr like

polkadot companion: paritytech/polkadot#567

or any other polkadot pr is mentioned in this pr's description and checks its 
status.


EOT


if ! [ "${CI_COMMIT_REF_NAME}" -gt 0 2>/dev/null ]
then
  boldprint "this doesn't seem to be a pull request"
  exit 1
fi

boldprint "this is pull request no ${CI_COMMIT_REF_NAME}"

companion="$(companion_pr "${CI_COMMIT_REF_NAME}" prnonly)"

if [ -z "${companion}" ]
then
  boldprint "no companion pr found"
  exit 0
fi

boldprint "companion pr: #${companion}"

check_mergeability "${companion}"

exit $?

