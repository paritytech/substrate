#!/usr/bin/env sh
cargo +nightly build --release -p node-cli --target wasm32-unknown-unknown --no-default-features --features browser -Z features=itarget
wasm-bindgen ../../../../target/wasm32-unknown-unknown/release/node_cli.wasm --out-dir pkg --target web
python -m SimpleHTTPServer 8000
