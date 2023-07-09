use std::{borrow::Cow, str::FromStr};

use codec::{Decode, Encode};
use sc_executor::{error::Result, WasmExecutor};
// use sc_executor_common::runtime_blob::RuntimeBlob;
use serde_json::{from_slice, Value};
use sp_core::{
	storage::Storage,
	traits::{CallContext, CodeExecutor, Externalities, FetchRuntimeCode, RuntimeCode},
};
use sp_genesis_builder::Result as BuildResult;
use sp_state_machine::BasicExternalities;

pub struct GenesisConfigBuilderRuntimeCaller<'a> {
	code: Cow<'a, [u8]>,
	code_hash: Vec<u8>,
	executor: WasmExecutor<sp_io::SubstrateHostFunctions>,
}

impl<'a> FetchRuntimeCode for GenesisConfigBuilderRuntimeCaller<'a> {
	fn fetch_runtime_code(&self) -> Option<Cow<[u8]>> {
		Some(self.code.as_ref().into())
	}
}

impl<'a> GenesisConfigBuilderRuntimeCaller<'a> {
	pub fn new(code: &'a [u8]) -> Self {
		GenesisConfigBuilderRuntimeCaller {
			code: code.into(),
			code_hash: sp_core::blake2_256(&code).to_vec(),
			executor: WasmExecutor::<sp_io::SubstrateHostFunctions>::builder().build(),
		}
	}

	fn call(&self, ext: &mut dyn Externalities, method: &str, data: &[u8]) -> Result<Vec<u8>> {
		self.executor
			.call(
				ext,
				&RuntimeCode { heap_pages: None, code_fetcher: self, hash: self.code_hash.clone() },
				method,
				data,
				false,
				CallContext::Offchain,
			)
			.0
	}
}

impl<'a> GenesisConfigBuilderRuntimeCaller<'a> {
	pub fn get_default_config(&self) -> core::result::Result<Value, String> {
		let mut t = BasicExternalities::new_empty();
		let call_result = self
			.call(&mut t, "GenesisBuilder_create_default_config", &vec![])
			.map_err(|e| format!("wasm call error {e}"))?;
		let default_config = Vec::<u8>::decode(&mut &call_result[..])
			.map_err(|e| format!("scale codec error: {e}"))?;
		Ok(from_slice(&default_config[..]).expect("returned value is json. qed."))
	}

	pub fn get_storage_for_config(&self, config: Value) -> core::result::Result<Storage, String> {
		let mut ext = BasicExternalities::new_empty();

		let call_result = self
			.call(&mut ext, "GenesisBuilder_build_config", &config.to_string().encode())
			.map_err(|e| format!("wasm call error {e}"))?;

		let build_result = BuildResult::decode(&mut &call_result[..])
			.map_err(|e| format!("scale codec error: {e}"))?;

		Ok(build_result.map(|_| ext.into_storages())?)
	}

	pub fn get_storage_for_patch(&self, patch: Value) -> core::result::Result<Storage, String> {
		let mut config = self.get_default_config()?;
		json_patch::merge(&mut config, &patch);
		self.get_storage_for_config(config)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	pub use sp_consensus_babe::{AllowedSlots, BabeEpochConfiguration, Slot};

	#[test]
	fn get_default_config_works() {
		sp_tracing::try_init_simple();
		let config =
			GenesisConfigBuilderRuntimeCaller::new(substrate_test_runtime::wasm_binary_unwrap())
				.get_default_config()
				.unwrap();
		let expected = r#"{"system":{},"babe":{"authorities":[],"epochConfig":null},"substrateTest":{"authorities":[]},"balances":{"balances":[]}}"#;
		assert_eq!(serde_json::from_str::<Value>(expected).unwrap(), config);
	}

	#[test]
	fn get_storage_for_patch_works() {
		sp_tracing::try_init_simple();

		let patch = serde_json::json!({
			"babe": {
				"epochConfig": {
					"c": [
						69,
						696
					],
					"allowed_slots": "PrimaryAndSecondaryPlainSlots"
				}
			},
		});

		let storage =
			GenesisConfigBuilderRuntimeCaller::new(substrate_test_runtime::wasm_binary_unwrap())
				.get_storage_for_patch(patch)
				.unwrap();

		//Babe|Authorities
		let value: Vec<u8> = storage
			.top
			.get(
				&array_bytes::hex2bytes(
					"1cb6f36e027abb2091cfb5110ab5087fdc6b171b77304263c292cc3ea5ed31ef",
				)
				.unwrap(),
			)
			.unwrap()
			.clone();

		assert_eq!(
			BabeEpochConfiguration::decode(&mut &value[..]).unwrap(),
			BabeEpochConfiguration {
				c: (69, 696),
				allowed_slots: AllowedSlots::PrimaryAndSecondaryPlainSlots
			}
		);
	}
}
