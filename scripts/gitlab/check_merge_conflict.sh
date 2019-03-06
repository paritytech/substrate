#!/bin/sh
#
# check if there is a merge conflict with this pull request only about wasm 
# binary blobs. if so trigger a rebuild of it and push it on the feature 
# branch if owned by paritytech
#

set -e # fail on any error

TEST_RUNTIME="core/test-runtime/wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm"
NODE_RUNTIME="node/runtime/wasm/target/wasm32-unknown-unknown/release/node_runtime.compact.wasm"



jsonfile="$(mktemp)"

attemptno="1"
while ( ! test -s ${jsonfile} ) \
	|| ( [ "$(jq -r .mergeable ${jsonfile})" = "null" ] \
	     && [ "${attemptno}" -lt 5 ] )
do
	echo "|  checking pull request status (attempt no ${attemptno})"
	curl -sS -o ${jsonfile} -H "Accept: application/vnd.github.v3+json" \
	  "${GITHUB_API}/repos/paritytech/substrate/pulls/${CI_COMMIT_REF_NAME}"
	sleep 3
	attemptno="$(( ${attemptno} + 1 ))"
done



baseref="$(jq -r .head.ref ${jsonfile})"
baserepo="$(jq -r .head.repo.full_name ${jsonfile})"
mergeable="$(jq -r .mergeable ${jsonfile})"

rm -f ${jsonfile}


cat <<-EOT
|
|  pr is of feature branch ${baseref} on ${baserepo}
|
|  tell me github is this branch mergeable into the master branch?
|
EOT

test "${mergeable}" = "true" && echo "|  yes, it is." && exit 0

if [ "${baseref}" = "null" -o "${baserepo}" = "null" ]
then
	echo "| either connectivity issues with github or pull request not existant"
	exit 3
fi

cat <<-EOT
|  not mergeable
|
|  github sees a conflict - check if it's only about the following wasm blobs
|
|	- ${TEST_RUNTIME}
|	- ${NODE_RUNTIME}
|
EOT

git fetch origin master
git config --global user.email "devops-team+substrate-ci-merge-conflict@parity.io"
git config --global user.name "I shall never commit to anything"

cat <<-EOT
|
|  trying to merge with the master branch to see if there is a conflict about
|  the wasm files only
|
EOT

if git merge --no-commit --no-ff origin/master | grep '^CONFLICT ' \
	| grep -v -e ${TEST_RUNTIME} -e ${NODE_RUNTIME}
then
  git merge --abort
	echo "|  there are more conflicting files than the wasm blobs"
	exit 1
fi
git merge --abort


cat <<-EOT
|
|  only wasm blobs block the merge.
|
|  triggering rebuild of wasm blobs which will be pushed onto the feature 
|  branch of this pull request upon success.
| 
|  see:
|
EOT



curl -sS -X POST \
	-F "token=${CI_JOB_TOKEN}" \
	-F "ref=master" \
	-F "variables[REBUILD_WASM]=\"${baserepo}:${baseref}\"" \
	${GITLAB_API}/projects/${GITHUB_API_PROJECT}/trigger/pipeline \
	| jq -r .web_url

# fail as there will be another commit on top of that feature branch that will
# be tested anyway.
exit 1


# vim: noexpandtab
