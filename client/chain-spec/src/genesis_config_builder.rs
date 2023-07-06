use codec::{Decode, Encode};
use sc_executor::{error::Result, WasmExecutor};
use sc_executor_common::runtime_blob::RuntimeBlob;
use serde_json::{from_slice, Value};
use sp_core::{storage::Storage, traits::Externalities};
use sp_genesis_builder::Result as BuildResult;
use sp_state_machine::BasicExternalities;

// todo:
// - tests: focus on errors
// - reuse executor
// - pub api + internal function

fn executor_call(
	ext: &mut dyn Externalities,
	code: &[u8],
	method: &str,
	data: &[u8],
) -> Result<Vec<u8>> {
	WasmExecutor::<sp_io::SubstrateHostFunctions>::builder().build().uncached_call(
		RuntimeBlob::uncompress_if_needed(code.into()).unwrap(),
		ext,
		true,
		method,
		data,
	)
}

pub fn get_storage_for_config(code: &[u8], config: Value) -> core::result::Result<Storage, String> {
	log::info!("get_storage_for_config: {:?}", config);
	let mut ext = BasicExternalities::new_empty();

	let call_result =
		executor_call(&mut ext, code, "GenesisBuilder_build_config", &config.to_string().encode())
			.map_err(|e| format!("wasm call error {e}"))?;

	log::info!("get_storage_for_config: call_restul {:?}", call_result);
	log::info!("get_storage_for_config: ext {:?}", ext);
	let build_result = BuildResult::decode(&mut &call_result[..])
		.map_err(|e| format!("scale codec error: {e}"))?;
	log::info!("get_storage_for_config: br {:?}", build_result);

	Ok(build_result.map(|_| ext.into_storages())?)
}

pub fn get_storage_for_patch(code: &[u8], patch: Value) -> core::result::Result<Storage, String> {
	log::info!("get_storage_for_patch: {:?}", patch);
	let mut t = BasicExternalities::new_empty();
	let call_result = executor_call(&mut t, code, "GenesisBuilder_create_default_config", &vec![])
		.map_err(|e| format!("wasm call error {e}"))?;

	let default_config =
		Vec::<u8>::decode(&mut &call_result[..]).map_err(|e| format!("scale codec error: {e}"))?;

	let mut config: Value = from_slice(&default_config[..]).expect("returned value is json. qed.");

	json_patch::merge(&mut config, &patch);
	get_storage_for_config(code, config)
}

// pub fn get_default_config(code: &[u8]) -> core::result::Result<Storage, String> {
// 	let mut t = BasicExternalities::new_empty();
// 	let call_result = executor_call(&mut t, code, "GenesisBuilder_create_default_config", &vec![])
// 		.map_err(|e| format!("wasm call error {e}"))?;

// 	let default_config =
// 		Vec::<u8>::decode(&mut &call_result[..]).map_err(|e| format!("scale codec error: {e}"))?;

// 	let mut config: Value = from_slice(&default_config[..]).expect("returned value is json. qed.");

// 	json_patch::merge(&mut config, &patch);
// 	get_storage_for_config(code, config)
// }

// #[test]
// fn build_config_from_json_works() {
// 	sp_tracing::try_init_simple();
// 	let j = include_str!("../../../test-utils/runtime/src/test_json/default_genesis_config.json");

// 	let mut t = BasicExternalities::new_empty();
// 	let r = executor_call(&mut t, "GenesisBuilder_build_config", &j.encode()).unwrap();
// 	let r = BuildResult::decode(&mut &r[..]);
// 	assert!(r.is_ok());

// 	// let mut _keys = t.into_storages().top.keys().cloned().map(hex).collect::<Vec<String>>();
// }
