// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Running
//! Running this test can be done with
//! ```text
//! wasm-pack test --firefox --release --headless bin/node/browser-testing
//! ```
//! or (without `wasm-pack`)
//! ```text
//! CARGO_TARGET_WASM32_UNKNOWN_UNKNOWN_RUNNER=wasm-bindgen-test-runner WASM_BINDGEN_TEST_TIMEOUT=60 cargo test --target wasm32-unknown-unknown
//! ```
//! For debug information, such as the informant, run without the `--headless`
//! flag and open a browser to the url that `wasm-pack test` outputs.
//! For more information see <https://rustwasm.github.io/docs/wasm-pack/>.

use jsonrpsee_types::v2::{
	params::{Id, JsonRpcParams},
	request::JsonRpcCallSer,
	response::JsonRpcResponse,
};
use serde::de::DeserializeOwned;
use wasm_bindgen::JsValue;
use wasm_bindgen_futures::JsFuture;
use wasm_bindgen_test::{wasm_bindgen_test, wasm_bindgen_test_configure};

wasm_bindgen_test_configure!(run_in_browser);

fn rpc_call(method: &str) -> String {
	serde_json::to_string(&JsonRpcCallSer::new(Id::Number(1), method, JsonRpcParams::NoParams))
		.unwrap()
}

fn deserialize_rpc_result<T: DeserializeOwned>(js_value: JsValue) -> T {
	let string = js_value.as_string().unwrap();
	let val = serde_json::from_str::<JsonRpcResponse<T>>(&string).unwrap().result;
	val
}

#[wasm_bindgen_test]
async fn runs() {
	let mut client = node_cli::start_client(None, "info".into()).unwrap();

	// Check that the node handles rpc calls.
	// TODO: Re-add the code that checks if the node is syncing.
	let chain_name: String = deserialize_rpc_result(
		JsFuture::from(client.rpc_send(&rpc_call("system_chain"))).await.unwrap(),
	);
	assert_eq!(chain_name, "Development");
}
