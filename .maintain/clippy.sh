#!/usr/bin/env sh

# Script for building only the WASM binary of the given project.

set -e

SKIP_WASM_BUILD=1 cargo +nightly clippy -- \
-A clippy::all \
-D clippy::correctness \
-A clippy::if-same-then-else \
-A clippy::clone-double-ref
