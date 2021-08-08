// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Substrate chain configurations.
#![warn(missing_docs)]

use crate::{extension::GetExtension, ChainType, Properties, RuntimeGenesis};
use sc_network::config::MultiaddrWithPeerId;
use sc_telemetry::TelemetryEndpoints;
use serde::{Deserialize, Serialize};
use serde_json as json;
use sp_core::{
	storage::{ChildInfo, Storage, StorageChild, StorageData, StorageKey},
	Bytes,
};
use sp_runtime::BuildStorage;
use std::{borrow::Cow, collections::HashMap, fs::File, path::PathBuf, sync::Arc};

enum GenesisSource<G> {
	File(PathBuf),
	Binary(Cow<'static, [u8]>),
	Factory(Arc<dyn Fn() -> G + Send + Sync>),
	Storage(Storage),
}

impl<G> Clone for GenesisSource<G> {
	fn clone(&self) -> Self {
		match *self {
			Self::File(ref path) => Self::File(path.clone()),
			Self::Binary(ref d) => Self::Binary(d.clone()),
			Self::Factory(ref f) => Self::Factory(f.clone()),
			Self::Storage(ref s) => Self::Storage(s.clone()),
		}
	}
}

impl<G: RuntimeGenesis> GenesisSource<G> {
	fn resolve(&self) -> Result<Genesis<G>, String> {
		#[derive(Serialize, Deserialize)]
		struct GenesisContainer<G> {
			genesis: Genesis<G>,
		}

		match self {
			Self::File(path) => {
				let file =
					File::open(path).map_err(|e| format!("Error opening spec file: {}", e))?;
				let genesis: GenesisContainer<G> = json::from_reader(file)
					.map_err(|e| format!("Error parsing spec file: {}", e))?;
				Ok(genesis.genesis)
			},
			Self::Binary(buf) => {
				let genesis: GenesisContainer<G> = json::from_reader(buf.as_ref())
					.map_err(|e| format!("Error parsing embedded file: {}", e))?;
				Ok(genesis.genesis)
			},
			Self::Factory(f) => Ok(Genesis::Runtime(f())),
			Self::Storage(storage) => {
				let top = storage
					.top
					.iter()
					.map(|(k, v)| (StorageKey(k.clone()), StorageData(v.clone())))
					.collect();

				let children_default = storage
					.children_default
					.iter()
					.map(|(k, child)| {
						(
							StorageKey(k.clone()),
							child
								.data
								.iter()
								.map(|(k, v)| (StorageKey(k.clone()), StorageData(v.clone())))
								.collect(),
						)
					})
					.collect();

				Ok(Genesis::Raw(RawGenesis { top, children_default }))
			},
		}
	}
}

impl<G: RuntimeGenesis, E> BuildStorage for ChainSpec<G, E> {
	fn build_storage(&self) -> Result<Storage, String> {
		match self.genesis.resolve()? {
			Genesis::Runtime(gc) => gc.build_storage(),
			Genesis::Raw(RawGenesis { top: map, children_default: children_map }) => Ok(Storage {
				top: map.into_iter().map(|(k, v)| (k.0, v.0)).collect(),
				children_default: children_map
					.into_iter()
					.map(|(storage_key, child_content)| {
						let child_info = ChildInfo::new_default(storage_key.0.as_slice());
						(
							storage_key.0,
							StorageChild {
								data: child_content.into_iter().map(|(k, v)| (k.0, v.0)).collect(),
								child_info,
							},
						)
					})
					.collect(),
			}),
		}
	}

	fn assimilate_storage(&self, _: &mut Storage) -> Result<(), String> {
		Err("`assimilate_storage` not implemented for `ChainSpec`.".into())
	}
}

pub type GenesisStorage = HashMap<StorageKey, StorageData>;

/// Raw storage content for genesis block.
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct RawGenesis {
	pub top: GenesisStorage,
	pub children_default: HashMap<StorageKey, GenesisStorage>,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
enum Genesis<G> {
	Runtime(G),
	Raw(RawGenesis),
}

/// A configuration of a client. Does not include runtime storage initialization.
#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
struct ClientSpec<E> {
	name: String,
	id: String,
	#[serde(default)]
	chain_type: ChainType,
	boot_nodes: Vec<MultiaddrWithPeerId>,
	telemetry_endpoints: Option<TelemetryEndpoints>,
	protocol_id: Option<String>,
	properties: Option<Properties>,
	#[serde(flatten)]
	extensions: E,
	// Never used, left only for backward compatibility.
	consensus_engine: (),
	#[serde(skip_serializing)]
	genesis: serde::de::IgnoredAny,
	/// Mapping from `block_hash` to `wasm_code`.
	///
	/// The given `wasm_code` will be used to substitute the on-chain wasm code from the given
	/// block hash onwards.
	#[serde(default)]
	code_substitutes: HashMap<String, Bytes>,
}

/// A type denoting empty extensions.
///
/// We use `Option` here since `()` is not flattenable by serde.
pub type NoExtension = Option<()>;

/// A configuration of a chain. Can be used to build a genesis block.
pub struct ChainSpec<G, E = NoExtension> {
	client_spec: ClientSpec<E>,
	genesis: GenesisSource<G>,
}

impl<G, E: Clone> Clone for ChainSpec<G, E> {
	fn clone(&self) -> Self {
		ChainSpec { client_spec: self.client_spec.clone(), genesis: self.genesis.clone() }
	}
}

impl<G, E> ChainSpec<G, E> {
	/// A list of bootnode addresses.
	pub fn boot_nodes(&self) -> &[MultiaddrWithPeerId] {
		&self.client_spec.boot_nodes
	}

	/// Spec name.
	pub fn name(&self) -> &str {
		&self.client_spec.name
	}

	/// Spec id.
	pub fn id(&self) -> &str {
		&self.client_spec.id
	}

	/// Telemetry endpoints (if any)
	pub fn telemetry_endpoints(&self) -> &Option<TelemetryEndpoints> {
		&self.client_spec.telemetry_endpoints
	}

	/// Network protocol id.
	pub fn protocol_id(&self) -> Option<&str> {
		self.client_spec.protocol_id.as_ref().map(String::as_str)
	}

	/// Additional loosly-typed properties of the chain.
	///
	/// Returns an empty JSON object if 'properties' not defined in config
	pub fn properties(&self) -> Properties {
		self.client_spec.properties.as_ref().unwrap_or(&json::map::Map::new()).clone()
	}

	/// Add a bootnode to the list.
	pub fn add_boot_node(&mut self, addr: MultiaddrWithPeerId) {
		self.client_spec.boot_nodes.push(addr)
	}

	/// Returns a reference to the defined chain spec extensions.
	pub fn extensions(&self) -> &E {
		&self.client_spec.extensions
	}

	/// Returns a mutable reference to the defined chain spec extensions.
	pub fn extensions_mut(&mut self) -> &mut E {
		&mut self.client_spec.extensions
	}

	/// Create hardcoded spec.
	pub fn from_genesis<F: Fn() -> G + 'static + Send + Sync>(
		name: &str,
		id: &str,
		chain_type: ChainType,
		constructor: F,
		boot_nodes: Vec<MultiaddrWithPeerId>,
		telemetry_endpoints: Option<TelemetryEndpoints>,
		protocol_id: Option<&str>,
		properties: Option<Properties>,
		extensions: E,
	) -> Self {
		let client_spec = ClientSpec {
			name: name.to_owned(),
			id: id.to_owned(),
			chain_type,
			boot_nodes,
			telemetry_endpoints,
			protocol_id: protocol_id.map(str::to_owned),
			properties,
			extensions,
			consensus_engine: (),
			genesis: Default::default(),
			code_substitutes: HashMap::new(),
		};

		ChainSpec { client_spec, genesis: GenesisSource::Factory(Arc::new(constructor)) }
	}

	/// Type of the chain.
	fn chain_type(&self) -> ChainType {
		self.client_spec.chain_type.clone()
	}
}

impl<G, E: serde::de::DeserializeOwned> ChainSpec<G, E> {
	/// Parse json content into a `ChainSpec`
	pub fn from_json_bytes(json: impl Into<Cow<'static, [u8]>>) -> Result<Self, String> {
		let json = json.into();
		let client_spec = json::from_slice(json.as_ref())
			.map_err(|e| format!("Error parsing spec file: {}", e))?;
		Ok(ChainSpec { client_spec, genesis: GenesisSource::Binary(json) })
	}

	/// Parse json file into a `ChainSpec`
	pub fn from_json_file(path: PathBuf) -> Result<Self, String> {
		let file = File::open(&path).map_err(|e| format!("Error opening spec file: {}", e))?;
		let client_spec =
			json::from_reader(file).map_err(|e| format!("Error parsing spec file: {}", e))?;
		Ok(ChainSpec { client_spec, genesis: GenesisSource::File(path) })
	}
}

#[derive(Serialize, Deserialize)]
struct JsonContainer<G, E> {
	#[serde(flatten)]
	client_spec: ClientSpec<E>,
	genesis: Genesis<G>,
}

impl<G: RuntimeGenesis, E: serde::Serialize + Clone + 'static> ChainSpec<G, E> {
	fn json_container(&self, raw: bool) -> Result<JsonContainer<G, E>, String> {
		let genesis = match (raw, self.genesis.resolve()?) {
			(true, Genesis::Runtime(g)) => {
				let storage = g.build_storage()?;
				let top =
					storage.top.into_iter().map(|(k, v)| (StorageKey(k), StorageData(v))).collect();
				let children_default = storage
					.children_default
					.into_iter()
					.map(|(sk, child)| {
						(
							StorageKey(sk),
							child
								.data
								.into_iter()
								.map(|(k, v)| (StorageKey(k), StorageData(v)))
								.collect(),
						)
					})
					.collect();

				Genesis::Raw(RawGenesis { top, children_default })
			},
			(_, genesis) => genesis,
		};
		Ok(JsonContainer { client_spec: self.client_spec.clone(), genesis })
	}

	/// Dump to json string.
	pub fn as_json(&self, raw: bool) -> Result<String, String> {
		let container = self.json_container(raw)?;
		json::to_string_pretty(&container).map_err(|e| format!("Error generating spec json: {}", e))
	}
}

impl<G, E> crate::ChainSpec for ChainSpec<G, E>
where
	G: RuntimeGenesis + 'static,
	E: GetExtension + serde::Serialize + Clone + Send + Sync + 'static,
{
	fn boot_nodes(&self) -> &[MultiaddrWithPeerId] {
		ChainSpec::boot_nodes(self)
	}

	fn name(&self) -> &str {
		ChainSpec::name(self)
	}

	fn id(&self) -> &str {
		ChainSpec::id(self)
	}

	fn chain_type(&self) -> ChainType {
		ChainSpec::chain_type(self)
	}

	fn telemetry_endpoints(&self) -> &Option<TelemetryEndpoints> {
		ChainSpec::telemetry_endpoints(self)
	}

	fn protocol_id(&self) -> Option<&str> {
		ChainSpec::protocol_id(self)
	}

	fn properties(&self) -> Properties {
		ChainSpec::properties(self)
	}

	fn add_boot_node(&mut self, addr: MultiaddrWithPeerId) {
		ChainSpec::add_boot_node(self, addr)
	}

	fn extensions(&self) -> &dyn GetExtension {
		ChainSpec::extensions(self) as &dyn GetExtension
	}

	fn extensions_mut(&mut self) -> &mut dyn GetExtension {
		ChainSpec::extensions_mut(self) as &mut dyn GetExtension
	}

	fn as_json(&self, raw: bool) -> Result<String, String> {
		ChainSpec::as_json(self, raw)
	}

	fn as_storage_builder(&self) -> &dyn BuildStorage {
		self
	}

	fn cloned_box(&self) -> Box<dyn crate::ChainSpec> {
		Box::new(self.clone())
	}

	fn set_storage(&mut self, storage: Storage) {
		self.genesis = GenesisSource::Storage(storage);
	}

	fn code_substitutes(&self) -> std::collections::HashMap<String, Vec<u8>> {
		self.client_spec
			.code_substitutes
			.iter()
			.map(|(h, c)| (h.clone(), c.0.clone()))
			.collect()
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[derive(Debug, Serialize, Deserialize)]
	struct Genesis(HashMap<String, String>);

	impl BuildStorage for Genesis {
		fn assimilate_storage(&self, storage: &mut Storage) -> Result<(), String> {
			storage.top.extend(
				self.0.iter().map(|(a, b)| (a.clone().into_bytes(), b.clone().into_bytes())),
			);
			Ok(())
		}
	}

	type TestSpec = ChainSpec<Genesis>;

	#[test]
	fn should_deserialize_example_chain_spec() {
		let spec1 = TestSpec::from_json_bytes(Cow::Owned(
			include_bytes!("../res/chain_spec.json").to_vec(),
		))
		.unwrap();
		let spec2 = TestSpec::from_json_file(PathBuf::from("./res/chain_spec.json")).unwrap();

		assert_eq!(spec1.as_json(false), spec2.as_json(false));
		assert_eq!(spec2.chain_type(), ChainType::Live)
	}

	#[derive(Debug, Serialize, Deserialize)]
	#[serde(rename_all = "camelCase")]
	struct Extension1 {
		my_property: String,
	}

	type TestSpec2 = ChainSpec<Genesis, Extension1>;

	#[test]
	fn should_deserialize_chain_spec_with_extensions() {
		let spec = TestSpec2::from_json_bytes(Cow::Owned(
			include_bytes!("../res/chain_spec2.json").to_vec(),
		))
		.unwrap();

		assert_eq!(spec.extensions().my_property, "Test Extension");
	}
}
