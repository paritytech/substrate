#!/bin/bash --
set -euo pipefail
PATH=~/.local/bin:~/.cargo/bin:/usr/local/bin:/usr/bin
cargo check --all
cargo test --all --release
cargo run -- purge-chain --dev
cargo run -- --dev
