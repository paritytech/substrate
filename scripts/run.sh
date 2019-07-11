#!/bin/sh --
set -eu
PATH=~/.local/bin:~/.cargo/bin:/usr/local/bin:/usr/bin:/bin
export PATH RUST_BACKTRACE=1 CARGO_INCREMENTAL=1
unset RUSTC_WRAPPER RUSTFLAGS LD_LIBRARY_PATH LD_RUN_PATH DYLD_LIBRARY_PATH || :
cargo check --all
cargo test --all --release
cargo run -- purge-chain --dev
exec cargo run -- --dev
