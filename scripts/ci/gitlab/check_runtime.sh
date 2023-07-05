#!/bin/sh
#
#
# check for any changes in the node/src/runtime, frame/ and primitives/sr_* trees. if
# there are any changes found, it should mark the PR breaksconsensus and
# "auto-fail" the PR if there isn't a change in the runtime/src/lib.rs file
# that alters the version.

set -e # fail on any error

#shellcheck source=../common/lib.sh
. "$(dirname "${0}")/../common/lib.sh"

VERSIONS_FILE="bin/node/runtime/src/lib.rs"

boldprint () { printf "|\n| \033[1m%s\033[0m\n|\n" "${@}"; }
boldcat () { printf "|\n"; while read -r l; do printf "| \033[1m%s\033[0m\n" "${l}"; done; printf "|\n" ; }

github_label () {
	echo
	echo "# run github-api job for labeling it ${1}"
	curl -sS -X POST \
		-F "token=${CI_JOB_TOKEN}" \
		-F "ref=master" \
		-F "variables[LABEL]=${1}" \
		-F "variables[PRNO]=${CI_COMMIT_REF_NAME}" \
		"${GITLAB_API}/projects/${GITHUB_API_PROJECT}/trigger/pipeline"
}


boldprint "latest 10 commits of ${CI_COMMIT_REF_NAME}"
git log --graph --oneline --decorate=short -n 10

boldprint "make sure the master branch and release tag are available in shallow clones"
git fetch --depth="${GIT_DEPTH:-100}" origin master
git fetch --depth="${GIT_DEPTH:-100}" origin release
git tag -f release FETCH_HEAD
git log -n1 release


boldprint "check if the wasm sources changed"
if ! has_runtime_changes origin/master "${CI_COMMIT_SHA}"
then
	boldcat <<-EOT

	no changes to the runtime source code detected

	EOT

	exit 0
fi



# check for spec_version updates: if the spec versions changed, then there is
# consensus-critical logic that has changed. the runtime wasm blobs must be
# rebuilt.

add_spec_version="$(git diff tags/release ${CI_COMMIT_SHA} -- "${VERSIONS_FILE}" \
	| sed -n -r "s/^\+[[:space:]]+spec_version: +([0-9]+),$/\1/p")"
sub_spec_version="$(git diff tags/release ${CI_COMMIT_SHA} -- "${VERSIONS_FILE}" \
	| sed -n -r "s/^\-[[:space:]]+spec_version: +([0-9]+),$/\1/p")"



if [ "${add_spec_version}" != "${sub_spec_version}" ]
then

	boldcat <<-EOT

		changes to the runtime sources and changes in the spec version.

		spec_version: ${sub_spec_version} -> ${add_spec_version}

	EOT
	exit 0

else
	# check for impl_version updates: if only the impl versions changed, we assume
	# there is no consensus-critical logic that has changed.

	add_impl_version="$(git diff tags/release ${CI_COMMIT_SHA} -- "${VERSIONS_FILE}" \
		| sed -n -r 's/^\+[[:space:]]+impl_version: +([0-9]+),$/\1/p')"
	sub_impl_version="$(git diff tags/release ${CI_COMMIT_SHA} -- "${VERSIONS_FILE}" \
		| sed -n -r 's/^\-[[:space:]]+impl_version: +([0-9]+),$/\1/p')"


	# see if the impl version changed
	if [ "${add_impl_version}" != "${sub_impl_version}" ]
	then
		boldcat <<-EOT

		changes to the runtime sources and changes in the impl version.

		impl_version: ${sub_impl_version} -> ${add_impl_version}

		EOT
		exit 0
	fi


	boldcat <<-EOT

	wasm source files changed but not the spec/impl version. If changes made do not alter logic,
	just bump 'impl_version'. If they do change logic, bump 'spec_version'.

	source file directories:
	- bin/node/src/runtime
	- frame
	- primitives/sr-*

	versions file: ${VERSIONS_FILE}

	EOT
fi

# dropped through. there's something wrong;  exit 1.

exit 1

# vim: noexpandtab
