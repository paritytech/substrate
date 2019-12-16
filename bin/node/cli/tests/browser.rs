use wasm_bindgen::prelude::*;
use wasm_bindgen_test::*;
use node_cli::start_client;

// run these tests using: wasm-pack test --firefox --headless -- --features wasm-bindgen
wasm_bindgen_test_configure!(run_in_browser);

#[wasm_bindgen(module = "/browser-demo/ws.js")]
extern "C" {
	fn ws() -> browser_utils::Transport;
}

#[wasm_bindgen_test]
async fn run() {
	let client = start_client(ws()).await;
}
