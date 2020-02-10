use wasm_bindgen_test::{wasm_bindgen_test, wasm_bindgen_test_configure};
use wasm_bindgen_futures::JsFuture;
use wasm_bindgen::JsValue;
use wasm_bindgen::prelude::wasm_bindgen;
use jsonrpc_core::types::{MethodCall, Success, Version, Params, Id};
use serde::de::DeserializeOwned;

wasm_bindgen_test_configure!(run_in_browser);

#[wasm_bindgen(module = "/src/ws.js")]
extern "C" {
    fn transport() -> libp2p::wasm_ext::ffi::Transport;
}

const CHAIN_SPEC: &str = include_str!("../../cli/res/flaming-fir.json");

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
    let mut client = node_cli::start_client(CHAIN_SPEC.into(), "info".into(), transport())
            .await
            .unwrap();

    // Give the node a bit of time to connect to peers.
    futures_timer::Delay::new(std::time::Duration::from_secs(5)).await;

    let state: sc_rpc_api::system::Health = deserialize_rpc_result(
        JsFuture::from(client.rpc_send(&rpc_call("system_health")))
            .await
            .unwrap()
    );

    assert!(state.should_have_peers);
    assert!(state.peers > 0);
    assert!(state.is_syncing);
}

