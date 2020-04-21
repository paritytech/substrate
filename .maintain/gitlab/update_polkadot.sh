#!/bin/sh
#
# update polkadot if a companion pull request was mentioned in the last 
# commit's description
#

. $(dirname $0)/lib.sh



boldcat <<-EOT


update_polkadot
==============

this job checks if there is a string in the description of the last commit like

polkadot companion: paritytech/polkadot#567

or another mentioning of a pull request on polkadot.


EOT



if [ "${CI_COMMIT_REF_NAME}" != "master" ]
then
  boldprint "polkadot:master is lock-stepping substrate:master"
  exit 1
fi


# get the last reference to a pr in polkadot from the latest pull request
pr_last="$(git show -s --format=format:%s | sed -r 's/^.*\(#([0-9]+)\)$/\1/')"

if [ -z "${pr_last}" ]
then
  boldprint "last commit was not a pull request"
  exit 1
fi

companion="$(companion_pr "${CI_COMMIT_REF_NAME}" prnonly)"

if [ -z "${companion}" ]
else
  boldprint "no companion pr found"
  exit 0
fi

boldprint "companion pr: #${companion}"


# check the status of that pull request - needs to be
# mergable and approved

check_mergeability "${companion}"

test "$?" = 0 || exit $?


# ready to merge polkadot pr


