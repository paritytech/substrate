# How to run this demo

```sh
cargo install wasm-pack		# If necessary

wasm-pack build --target web --out-dir ./browser-demo/pkg --no-typescript --release ./.. -- --no-default-features --features "browser"

xdg-open index.html
```
