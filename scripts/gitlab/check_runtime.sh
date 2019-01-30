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



# check if the wasm sources changed
if ! git diff --name-only origin/master...${CI_COMMIT_SHA} \
	| grep -e '^node/src/runtime' -e '^srml/' -e '^core/sr-'
then
	cat <<-EOT
	
	no changes to the runtime source code detected
	EOT
	exit 0
fi

# see if the version and the binary blob changed, too
if git diff master...${CI_COMMIT_SHA} node/runtime/src/lib.rs \
	| grep -q 'spec_version:' && \
	git diff --name-only master...${CI_COMMIT_SHA} \
	| grep -q "${RUNTIME}"
then
	cat <<-EOT
	
	changes to the runtime sources and changes in the spec version and wasm 
	binary blob.
	EOT
	exit 0
fi


cat <<-EOT

wasm source files changed but not the spec version or the runtime"
binary blob. This may break the api.

EOT





exit 1

# vim: noexpandtab
