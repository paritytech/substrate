cd ..
wasm-pack build --target web --out-dir ./browser-demo/pkg --no-typescript --release -- --no-default-features --features "browser"
cd browser-demo
python -m SimpleHTTPServer 8000
