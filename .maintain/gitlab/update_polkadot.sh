#!/bin/sh
#
# update polkadot if a companion pull request was mentioned in the last 
# commit's description
#


github_api_substrate_pull_url="https://api.github.com/repos/paritytech/substrate/pulls"
# use github api v3 in order to access the data without authentication
github_header="Accept: application/vnd.github.v3+json" 

boldprint () { printf "|\n| \033[1m${@}\033[0m\n|\n" ; }
boldcat () { printf "|\n"; while read l; do printf "| \033[1m${l}\033[0m\n"; done; printf "|\n" ; }



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

pr_body="$(curl -H "${github_header}" -s ${github_api_substrate_pull_url}/${pr_last} \
  | sed -n -r 's/^[[:space:]]+"body": (".*")[^"]+$/\1/p')"

# get companion if explicitly specified
pr_companion="$(echo "${pr_body}" | sed -n -r \
    -e 's;^.*polkadot companion: paritytech/polkadot#([0-9]+).*$;\1;p' \
    -e 's;^.*polkadot companion: https://github.com/paritytech/polkadot/pull/([0-9]+).*$;\1;p' \
  | tail -n 1)"

# get companion mentioned in the description
if [ -z "${pr_companion}" ]
then
  pr_companion="$(echo "${pr_body}" | sed -n -r \
    's;^.*https://github.com/paritytech/polkadot/pull/([0-9]+).*$;\1;p' \
    | tail -n 1)"
fi

if [ -z "${pr_companion}" ]
else
  boldprint "no companion pr found"
  exit 0
fi

boldprint "companion pr: #${pr_companion}"

# check the status of that pull request - needs to be
# mergable and approved


