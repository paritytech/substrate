# How to run this demo

```sh
cargo install wasm-pack		# If necessary

# From the `node/cli` directory (parent from this README)
wasm-pack build --target web --out-dir ./demo/pkg --no-typescript --release -- --no-default-features --features "browser"

xdg-open index.html
```
