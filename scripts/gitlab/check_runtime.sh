#!/bin/sh
#
#
# check for any changes in the node/src/runtime, srml/ and core/sr_* trees. if
# there are any changes found, it should mark the PR breaksconsensus and
# "auto-fail" the PR if there isn't a change in the runtime/src/lib.rs file 
# that alters the version.

set -e # fail on any error


# give some context
git log --graph --oneline --decorate=short -n 10


RUNTIME="node/runtime/wasm/target/wasm32-unknown-unknown/release/node_runtime.compact.wasm"
VERSIONS_FILE="node/runtime/src/lib.rs"

github_label () {
	echo
	echo "# run github-api job for labeling it ${1}"
	curl -sS -X POST \
		-F "token=${CI_JOB_TOKEN}" \
		-F "ref=master" \
		-F "variables[LABEL]=${1}" \
		-F "variables[PRNO]=${CI_COMMIT_REF_NAME}" \
		${GITLAB_API}/projects/${GITHUB_API_PROJECT}/trigger/pipeline
}




# check if the wasm sources changed
if ! git diff --name-only origin/master...${CI_COMMIT_SHA} \
	| grep -q -e '^node/src/runtime' -e '^srml/' -e '^core/sr-'
then
	cat <<-EOT
	
	no changes to the runtime source code detected

	EOT

	exit 0
fi



# check for spec_version updates: if the spec versions changed, then there is
# consensus-critical logic that has changed. the runtime wasm blobs must be
# rebuilt.

add_spec_version="$(git diff origin/master...${CI_COMMIT_SHA} ${VERSIONS_FILE} \
	| sed -n -r "s/^\+[[:space:]]+spec_version: +([0-9]+),$/\1/p")"
sub_spec_version="$(git diff origin/master...${CI_COMMIT_SHA} ${VERSIONS_FILE} \
	| sed -n -r "s/^\-[[:space:]]+spec_version: +([0-9]+),$/\1/p")"


# see if the version and the binary blob changed
if [ "${add_spec_version}" != "${sub_spec_version}" ]
then

	github_label "B2-breaksapi"

	cat <<-EOT
		
		changes to the runtime sources and changes in the spec version.
	
		spec_version: ${sub_spec_version} -> ${add_spec_version}
	
	EOT
	exit 0

else
	# check for impl_version updates: if only the impl versions changed, we assume
	# there is no consensus-critical logic that has changed.

	add_impl_version="$(git diff origin/master...${CI_COMMIT_SHA} ${VERSIONS_FILE} \
		| sed -n -r 's/^\+[[:space:]]+impl_version: +([0-9]+),$/\1/p')"
	sub_impl_version="$(git diff origin/master...${CI_COMMIT_SHA} ${VERSIONS_FILE} \
		| sed -n -r 's/^\-[[:space:]]+impl_version: +([0-9]+),$/\1/p')"


	# see if the impl version changed
	if [ "${add_impl_version}" != "${sub_impl_version}" ]
	then
		cat <<-EOT
		
		changes to the runtime sources and changes in the impl version.

		impl_version: ${sub_impl_version} -> ${add_impl_version}

		EOT
		exit 0
	fi


	cat <<-EOT

	wasm source files changed but not the spec/impl version and the runtime
	binary blob. If changes made do not alter logic, just bump 'impl_version'.
	If they do change logic, bump 'spec_version' and rebuild wasm.

	source file directories:
	- node/src/runtime
	- srml
	- core/sr-*

	versions file: ${VERSIONS_FILE}

	EOT

	# drop through into pushing `gotissues` and exit 1...
fi

# dropped through. there's something wrong; mark `gotissues` and exit 1.

github_label "A4-gotissues"


exit 1

# vim: noexpandtab
