#!/bin/sh
# 
# 
# check for any changes in the node/src/runtime, srml/ and core/sr_* trees. if 
# there are any changes found, it should mark the PR breaksconsensus and 
# "auto-fail" the PR in some way unless a) the runtime is rebuilt and b) there 
# isn't a change in the runtime/src/lib.rs file that alters the version.

set -e # fail on any error

# give some context
git log --graph --oneline --decorate=short -n 10


RUNTIME="node/runtime/wasm/target/wasm32-unknown-unknown/release/node_runtime.compact.wasm"
VERSIONS_FILE="node/runtime/src/lib.rs"



# check if the wasm sources changed
if ! git diff --name-only origin/master...${CI_COMMIT_SHA} \
	| grep -q -e '^node/src/runtime' -e '^srml/' -e '^core/sr-'
then
	cat <<-EOT
	
	no changes to the runtime source code detected

	EOT

	exit 0
fi



# check for version updates
for version in spec_version impl_version
do
	add_version="$(git diff origin/master...${CI_COMMIT_SHA} ${VERSIONS_FILE} \
		| sed -n -r "s/^\+[[:space:]]+${version}: +([0-9]+),$/\1/p")"
	sub_version="$(git diff origin/master...${CI_COMMIT_SHA} ${VERSIONS_FILE} \
		| sed -n -r "s/^\-[[:space:]]+${version}: +([0-9]+),$/\1/p")"
	
	
	# see if the version and the binary blob changed
	if git diff --name-only origin/master...${CI_COMMIT_SHA} \
		| grep -q "${RUNTIME}" && \
		[ "${add_version}" != "${sub_version}" ]
	then
		cat <<-EOT
		
		changes to the runtime sources and changes in the spec version and wasm 
		binary blob.
	
		${version}: ${sub_version} -> ${add_version}
	
		EOT
		exit 0
	fi
done




cat <<-EOT

wasm source files changed but not the spec version and the runtime
binary blob. This may break the api.

source file directories:
 - node/src/runtime
 - srml
 - core/sr-*

versions file: ${VERSIONS_FILE}


EOT

echo
echo "# run github-api job for labelling it breaksapi"
curl -sS -X POST \
	-F "token=${CI_JOB_TOKEN}" \
	-F "ref=master" \
	-F "variables[BREAKSAPI]=true" \
	-F "variables[PRNO]=${CI_COMMIT_REF_NAME}" \
	${GITLAB_API}/projects/${GITHUB_API_PROJECT}/trigger/pipeline
 



exit 1

# vim: noexpandtab
