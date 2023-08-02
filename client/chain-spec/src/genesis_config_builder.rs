// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! A helper module for calling the GenesisBuilder API from arbitrary runtime wasm blobs.

use codec::{Decode, Encode};
use sc_executor::{error::Result, WasmExecutor};
use serde_json::{from_slice, Value};
use sp_core::{
	storage::Storage,
	traits::{CallContext, CodeExecutor, Externalities, FetchRuntimeCode, RuntimeCode},
};
use sp_genesis_builder::Result as BuildResult;
use sp_state_machine::BasicExternalities;
use std::borrow::Cow;

/// A utility that facilitates calling the GenesisBuilder API from the runtime wasm code blob.
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
	/// Creates new instance using the provided code blob.
	pub fn new(code: &'a [u8]) -> Self {
		GenesisConfigBuilderRuntimeCaller {
			code: code.into(),
			code_hash: sp_core::blake2_256(&code).to_vec(),
			executor: WasmExecutor::<sp_io::SubstrateHostFunctions>::builder()
				.with_allow_missing_host_functions(true)
				.build(),
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
	/// Calls [`sp_genesis_builder::GenesisBuilder::create_default_config`] provided by runtime.
	pub fn get_default_config(&self) -> core::result::Result<Value, String> {
		let mut t = BasicExternalities::new_empty();
		let call_result = self
			.call(&mut t, "GenesisBuilder_create_default_config", &vec![])
			.map_err(|e| format!("wasm call error {e}"))?;
		let default_config = Vec::<u8>::decode(&mut &call_result[..])
			.map_err(|e| format!("scale codec error: {e}"))?;
		Ok(from_slice(&default_config[..]).expect("returned value is json. qed."))
	}

	/// Calls [`sp_genesis_builder::GenesisBuilder::build_config`] provided by runtime.
	pub fn get_storage_for_config(&self, config: Value) -> core::result::Result<Storage, String> {
		let mut ext = BasicExternalities::new_empty();

		let call_result = self
			.call(&mut ext, "GenesisBuilder_build_config", &config.to_string().encode())
			.map_err(|e| format!("wasm call error {e}"))?;

		BuildResult::decode(&mut &call_result[..])
			.map_err(|e| format!("scale codec error: {e}"))??;

		Ok(ext.into_storages())
	}

	/// Patch default `GenesisConfig` using given JSON patch and store it in the storage.
	///
	/// This function generates the `GenesisConfig` for the runtime by applying a provided JSON
	/// patch. The patch modifies the default `GenesisConfig` allowing customization of the specific
	/// keys. The resulting `GenesisConfig` is then deserialized from the patched JSON
	/// representation and stored in the storage.
	///
	/// If the provided JSON patch is incorrect or the deserialization fails the error will be
	/// returned.
	///
	/// The patching process modifies the default `GenesisConfig` according to the following rules:
	/// 1. Existing keys in the default configuration will be overridden by the corresponding values
	///    in the patch.
	/// 2. If a key exists in the patch but not in the default configuration, it will be added to
	///    the resulting `GenesisConfig`.
	/// 3. Keys in the default configuration that have null values in the patch will be removed from
	///    the resulting  `GenesisConfig`. This is helpful for changing enum variant value.
	///
	/// Please note that the patch may contain full `GenesisConfig`.
	pub fn get_storage_for_patch(&self, patch: Value) -> core::result::Result<Storage, String> {
		let mut config = self.get_default_config()?;
		json_patch::merge(&mut config, &patch);
		self.get_storage_for_config(config)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use serde_json::{from_str, json};
	pub use sp_consensus_babe::{AllowedSlots, BabeEpochConfiguration, Slot};

	#[test]
	fn get_default_config_works() {
		let config =
			GenesisConfigBuilderRuntimeCaller::new(substrate_test_runtime::wasm_binary_unwrap())
				.get_default_config()
				.unwrap();
		let expected = r#"{"system":{},"babe":{"authorities":[],"epochConfig":null},"substrateTest":{"authorities":[]},"balances":{"balances":[]}}"#;
		assert_eq!(from_str::<Value>(expected).unwrap(), config);
	}

	#[test]
	fn get_storage_for_patch_works() {
		let patch = json!({
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
