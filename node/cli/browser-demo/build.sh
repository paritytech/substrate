#!/usr/bin/env sh
wasm-pack build --target web --out-dir ./browser-demo/pkg --no-typescript --release ./.. -- --no-default-features --features "browser"
python -m SimpleHTTPServer 8000
