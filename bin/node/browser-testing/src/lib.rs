// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! # Running
//! Running this test can be done with
//! ```text
//! wasm-pack test --firefox --release --headless bin/node/browser-testing
//! ```
//! or (without `wasm-pack`)
//! ```text
//! CARGO_TARGET_WASM32_UNKNOWN_UNKNOWN_RUNNER=wasm-bindgen-test-runner WASM_BINDGEN_TEST_TIMEOUT=60 cargo test --target wasm32-unknown-unknown
//! ```
//! For debug infomation, such as the informant, run without the `--headless`
//! flag and open a browser to the url that `wasm-pack test` outputs.
//! For more infomation see https://rustwasm.github.io/docs/wasm-pack/.

use wasm_bindgen_test::{wasm_bindgen_test, wasm_bindgen_test_configure};
use wasm_bindgen_futures::JsFuture;
use wasm_bindgen::JsValue;
use jsonrpc_core::types::{MethodCall, Success, Version, Params, Id};
use serde::de::DeserializeOwned;

wasm_bindgen_test_configure!(run_in_browser);

fn rpc_call(method: &str) -> String {
    serde_json::to_string(&MethodCall {
        jsonrpc: Some(Version::V2),
        method: method.into(),
        params: Params::None,
        id: Id::Num(1)
    }).unwrap()
}

fn deserialize_rpc_result<T: DeserializeOwned>(js_value: JsValue) -> T {
    let string = js_value.as_string().unwrap();
    let value = serde_json::from_str::<Success>(&string).unwrap().result;
    // We need to convert a `Value::Object` into a proper type.
    let value_string = serde_json::to_string(&value).unwrap();
    serde_json::from_str(&value_string).unwrap()
}

#[wasm_bindgen_test]
async fn runs() {
    let mut client = node_cli::start_client(None, "info".into())
            .await
            .unwrap();

    // Check that the node handles rpc calls.
    // TODO: Re-add the code that checks if the node is syncing.
    let chain_name: String = deserialize_rpc_result(
        JsFuture::from(client.rpc_send(&rpc_call("system_chain")))
            .await
            .unwrap()
    );
    assert_eq!(chain_name, "Development");
}
