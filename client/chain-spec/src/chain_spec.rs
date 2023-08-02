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

//! Substrate chain configurations.
#![warn(missing_docs)]

use crate::{
	extension::GetExtension, ChainType, GenesisConfigBuilderRuntimeCaller as RuntimeCaller,
	Properties, RuntimeGenesis,
};
use sc_network::config::MultiaddrWithPeerId;
use sc_telemetry::TelemetryEndpoints;
use serde::{Deserialize, Serialize};
use serde_json as json;
use sp_core::{
	storage::{ChildInfo, Storage, StorageChild, StorageData, StorageKey},
	Bytes,
};
use sp_runtime::BuildStorage;
use std::{
	borrow::Cow, collections::BTreeMap, fs::File, marker::PhantomData, path::PathBuf, sync::Arc,
};

#[derive(Serialize, Deserialize, Clone)]
#[serde(rename_all = "camelCase")]
enum GenesisBuildAction {
	Patch(json::Value),
	Full(json::Value),
}

#[allow(deprecated)]
enum GenesisSource<G> {
	File(PathBuf),
	Binary(Cow<'static, [u8]>),
	#[deprecated(
		note = "Factory and G type parameter are planned to be removed in December 2023. Use `GenesisBuilderApi` instead."
	)]
	Factory(Arc<dyn Fn() -> G + Send + Sync>),
	Storage(Storage),
	GenesisBuilderApi(GenesisBuildAction),
}

impl<G> Clone for GenesisSource<G> {
	fn clone(&self) -> Self {
		match *self {
			Self::File(ref path) => Self::File(path.clone()),
			Self::Binary(ref d) => Self::Binary(d.clone()),
			#[allow(deprecated)]
			Self::Factory(ref f) => Self::Factory(f.clone()),
			Self::Storage(ref s) => Self::Storage(s.clone()),
			Self::GenesisBuilderApi(ref s) => Self::GenesisBuilderApi(s.clone()),
		}
	}
}

impl<G: RuntimeGenesis> GenesisSource<G> {
	fn resolve(&self) -> Result<Genesis<G>, String> {
		/// helper container for deserializing genesis from the JSON file (ChainSpec JSON file is
		/// also supported here)
		#[derive(Serialize, Deserialize)]
		struct GenesisContainer<G> {
			genesis: Genesis<G>,
		}

		match self {
			Self::File(path) => {
				let file = File::open(path).map_err(|e| {
					format!("Error opening spec file at `{}`: {}", path.display(), e)
				})?;
				// SAFETY: `mmap` is fundamentally unsafe since technically the file can change
				//         underneath us while it is mapped; in practice it's unlikely to be a
				//         problem
				let bytes = unsafe {
					memmap2::Mmap::map(&file).map_err(|e| {
						format!("Error mmaping spec file `{}`: {}", path.display(), e)
					})?
				};

				let genesis: GenesisContainer<G> = json::from_slice(&bytes)
					.map_err(|e| format!("Error parsing spec file: {}", e))?;
				Ok(genesis.genesis)
			},
			Self::Binary(buf) => {
				let genesis: GenesisContainer<G> = json::from_reader(buf.as_ref())
					.map_err(|e| format!("Error parsing embedded file: {}", e))?;
				Ok(genesis.genesis)
			},
			#[allow(deprecated)]
			Self::Factory(f) => Ok(Genesis::Runtime(f())),
			Self::Storage(storage) => Ok(Genesis::Raw(RawGenesis::from(storage.clone()))),
			Self::GenesisBuilderApi(GenesisBuildAction::Full(config)) =>
				Ok(Genesis::RuntimeGenesisConfig(config.clone())),
			Self::GenesisBuilderApi(GenesisBuildAction::Patch(patch)) =>
				Ok(Genesis::RuntimeGenesisConfigPatch(patch.clone())),
		}
	}
}

impl<G: RuntimeGenesis, E> BuildStorage for ChainSpec<G, E> {
	fn assimilate_storage(&self, storage: &mut Storage) -> Result<(), String> {
		match self.genesis.resolve()? {
			#[allow(deprecated)]
			Genesis::Runtime(gc) => gc.assimilate_storage(storage),
			Genesis::Raw(RawGenesis { top: map, children_default: children_map }) => {
				storage.top.extend(map.into_iter().map(|(k, v)| (k.0, v.0)));
				children_map.into_iter().for_each(|(k, v)| {
					let child_info = ChildInfo::new_default(k.0.as_slice());
					storage
						.children_default
						.entry(k.0)
						.or_insert_with(|| StorageChild { data: Default::default(), child_info })
						.data
						.extend(v.into_iter().map(|(k, v)| (k.0, v.0)));
				});
				Ok(())
			},
			// The `StateRootHash` variant exists as a way to keep note that other clients support
			// it, but Substrate itself isn't capable of loading chain specs with just a hash at the
			// moment.
			Genesis::StateRootHash(_) => Err("Genesis storage in hash format not supported".into()),
			Genesis::RuntimeGenesisConfig(config) => RuntimeCaller::new(&self.code[..])
				.get_storage_for_config(config)?
				.assimilate_storage(storage),
			Genesis::RuntimeGenesisConfigPatch(patch) => RuntimeCaller::new(&self.code[..])
				.get_storage_for_patch(patch)?
				.assimilate_storage(storage),
		}?;

		if !self.code.is_empty() {
			storage
				.top
				.insert(sp_core::storage::well_known_keys::CODE.to_vec(), self.code.clone());
		}

		Ok(())
	}
}

pub type GenesisStorage = BTreeMap<StorageKey, StorageData>;

/// Raw storage content for genesis block.
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct RawGenesis {
	pub top: GenesisStorage,
	pub children_default: BTreeMap<StorageKey, GenesisStorage>,
}

impl From<sp_core::storage::Storage> for RawGenesis {
	fn from(value: sp_core::storage::Storage) -> Self {
		Self {
			top: value.top.into_iter().map(|(k, v)| (StorageKey(k), StorageData(v))).collect(),
			children_default: value
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
				.collect(),
		}
	}
}

/// Represents different options for the GenesisConfig configuration.
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
enum Genesis<G> {
	/// [Deprecated] Contains the JSON representation of G (the native type representing the
	/// runtime GenesisConfig struct) (will be removed with `ChainSpec::from_genesis`).
	Runtime(G),
	/// The genesis storage as raw data.
	Raw(RawGenesis),
	/// State root hash of the genesis storage.
	StateRootHash(StorageData),
	/// Represents the full runtime genesis config in JSON format.
	/// The contained object is a JSON blob that can be parsed by a compatible runtime.
	RuntimeGenesisConfig(json::Value),
	/// Represents a patch for the default runtime genesis config in JSON format.
	/// The contained value is a JSON object that can be parsed by a compatible runtime.
	RuntimeGenesisConfigPatch(json::Value),
}

/// A configuration of a client. Does not include runtime storage initialization.
/// Note: `genesis` and `code` are ignored due to way how the chain specification is serialized into
/// JSON file. Refer to [`ChainSpecJsonContainer`], which flattens [`ClientSpec`] and denies uknown
/// fields.
#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(rename_all = "camelCase")]
struct ClientSpec<E> {
	name: String,
	id: String,
	#[serde(default)]
	chain_type: ChainType,
	boot_nodes: Vec<MultiaddrWithPeerId>,
	telemetry_endpoints: Option<TelemetryEndpoints>,
	protocol_id: Option<String>,
	/// Arbitrary string. Nodes will only synchronize with other nodes that have the same value
	/// in their `fork_id`. This can be used in order to segregate nodes in cases when multiple
	/// chains have the same genesis hash.
	#[serde(default = "Default::default", skip_serializing_if = "Option::is_none")]
	fork_id: Option<String>,
	properties: Option<Properties>,
	#[serde(flatten)]
	extensions: E,
	// Never used, left only for backward compatibility.
	#[serde(default, skip_serializing)]
	#[allow(unused)]
	consensus_engine: (),
	#[serde(skip_serializing)]
	#[allow(unused)]
	genesis: serde::de::IgnoredAny,
	#[serde(skip)]
	#[allow(unused)]
	code: serde::de::IgnoredAny,
	/// Mapping from `block_number` to `wasm_code`.
	///
	/// The given `wasm_code` will be used to substitute the on-chain wasm code starting with the
	/// given block number until the `spec_version` on chain changes.
	#[serde(default)]
	code_substitutes: BTreeMap<String, Bytes>,
}

/// A type denoting empty extensions.
///
/// We use `Option` here since `()` is not flattenable by serde.
pub type NoExtension = Option<()>;

/// Builder for creating [`ChainSpec`] instances.
pub struct ChainSpecBuilder<G, E = NoExtension> {
	name: Option<String>,
	id: Option<String>,
	chain_type: Option<ChainType>,
	boot_nodes: Option<Vec<MultiaddrWithPeerId>>,
	telemetry_endpoints: Option<TelemetryEndpoints>,
	protocol_id: Option<String>,
	fork_id: Option<String>,
	properties: Option<Properties>,
	extensions: Option<E>,
	code: Option<Vec<u8>>,
	genesis_build_action: Option<GenesisBuildAction>,
	_genesis: PhantomData<G>,
}

impl<G, E> ChainSpecBuilder<G, E> {
	/// Creates a new builder instance with no defaults.
	pub fn new() -> Self {
		Self {
			name: None,
			id: None,
			chain_type: None,
			boot_nodes: None,
			telemetry_endpoints: None,
			protocol_id: None,
			fork_id: None,
			properties: None,
			extensions: None,
			code: None,
			genesis_build_action: None,
			_genesis: Default::default(),
		}
	}

	/// Sets the spec name. This method must be called.
	pub fn with_name(mut self, name: &str) -> Self {
		self.name = Some(name.into());
		self
	}

	/// Sets the spec ID. This method must be called.
	pub fn with_id(mut self, id: &str) -> Self {
		self.id = Some(id.into());
		self
	}

	/// Sets the type of the chain. This method must be called.
	pub fn with_chain_type(mut self, chain_type: ChainType) -> Self {
		self.chain_type = Some(chain_type);
		self
	}

	/// Sets a list of bootnode addresses.
	pub fn with_boot_nodes(mut self, boot_nodes: Vec<MultiaddrWithPeerId>) -> Self {
		self.boot_nodes = Some(boot_nodes);
		self
	}

	/// Sets telemetry endpoints.
	pub fn with_telemetry_endpoints(mut self, telemetry_endpoints: TelemetryEndpoints) -> Self {
		self.telemetry_endpoints = Some(telemetry_endpoints);
		self
	}

	/// Sets the network protocol ID.
	pub fn with_protocol_id(mut self, protocol_id: &str) -> Self {
		self.protocol_id = Some(protocol_id.into());
		self
	}

	/// Sets an optional network fork identifier.
	pub fn with_fork_id(mut self, fork_id: &str) -> Self {
		self.fork_id = Some(fork_id.into());
		self
	}

	/// Sets additional loosely-typed properties of the chain.
	pub fn with_properties(mut self, properties: Properties) -> Self {
		self.properties = Some(properties);
		self
	}

	/// Sets chain spec extensions. This method must be called.
	pub fn with_extensions(mut self, extensions: E) -> Self {
		self.extensions = Some(extensions);
		self
	}

	/// Sets the code. This method must be called.
	pub fn with_code(mut self, code: &[u8]) -> Self {
		self.code = Some(code.into());
		self
	}

	/// Sets the JSON patch for runtime's GenesisConfig.
	pub fn with_genesis_config_patch(mut self, patch: json::Value) -> Self {
		self.genesis_build_action = Some(GenesisBuildAction::Patch(patch));
		self
	}

	/// Sets the full runtime's GenesisConfig JSON.
	pub fn with_genesis_config(mut self, config: json::Value) -> Self {
		self.genesis_build_action = Some(GenesisBuildAction::Full(config));
		self
	}

	/// Builds a [`ChainSpec`] instance using the provided settings.
	pub fn build(self) -> ChainSpec<G, E> {
		let client_spec = ClientSpec {
			name: self.name.expect("with_name must be called."),
			id: self.id.expect("with_id must be called."),
			chain_type: self.chain_type.expect("with_chain_type must be called."),
			boot_nodes: self.boot_nodes.unwrap_or(Default::default()),
			telemetry_endpoints: self.telemetry_endpoints,
			protocol_id: self.protocol_id,
			fork_id: self.fork_id,
			properties: self.properties,
			extensions: self.extensions.expect("with_extensions must be called"),
			consensus_engine: (),
			genesis: Default::default(),
			code: Default::default(),
			code_substitutes: BTreeMap::new(),
		};

		ChainSpec {
			client_spec,
			genesis: GenesisSource::GenesisBuilderApi(
				self.genesis_build_action
					.expect("with_genesis_config_patch or with_genesis_config must be called."),
			),
			code: self.code.expect("with code must be called.").into(),
		}
	}
}

/// A configuration of a chain. Can be used to build a genesis block.
pub struct ChainSpec<G, E = NoExtension> {
	client_spec: ClientSpec<E>,
	genesis: GenesisSource<G>,
	code: Vec<u8>,
}

impl<G, E: Clone> Clone for ChainSpec<G, E> {
	fn clone(&self) -> Self {
		ChainSpec {
			client_spec: self.client_spec.clone(),
			genesis: self.genesis.clone(),
			code: self.code.clone(),
		}
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
		self.client_spec.protocol_id.as_deref()
	}

	/// Optional network fork identifier.
	pub fn fork_id(&self) -> Option<&str> {
		self.client_spec.fork_id.as_deref()
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
	#[deprecated(
		note = "`from_genesis` is planned to be removed in December 2023. Use `builder()` instead."
	)]
	// deprecated note: Genesis<G>::Runtime + GenesisSource::Factory shall also be removed
	pub fn from_genesis<F: Fn() -> G + 'static + Send + Sync>(
		name: &str,
		id: &str,
		chain_type: ChainType,
		constructor: F,
		boot_nodes: Vec<MultiaddrWithPeerId>,
		telemetry_endpoints: Option<TelemetryEndpoints>,
		protocol_id: Option<&str>,
		fork_id: Option<&str>,
		properties: Option<Properties>,
		extensions: E,
		code: &[u8],
	) -> Self {
		let client_spec = ClientSpec {
			name: name.to_owned(),
			id: id.to_owned(),
			chain_type,
			boot_nodes,
			telemetry_endpoints,
			protocol_id: protocol_id.map(str::to_owned),
			fork_id: fork_id.map(str::to_owned),
			properties,
			extensions,
			consensus_engine: (),
			genesis: Default::default(),
			code: Default::default(),
			code_substitutes: BTreeMap::new(),
		};

		#[allow(deprecated)]
		ChainSpec {
			client_spec,
			genesis: GenesisSource::Factory(Arc::new(constructor)),
			code: code.into(),
		}
	}

	/// Type of the chain.
	fn chain_type(&self) -> ChainType {
		self.client_spec.chain_type.clone()
	}

	/// Sets the code.
	pub fn set_code(&mut self, code: &[u8]) {
		self.code = code.into();
	}

	/// Provides a `ChainSpec` builder.
	pub fn builder() -> ChainSpecBuilder<G, E> {
		ChainSpecBuilder::new()
	}
}

/// Helper structure for deserializing optional `code` attribute from JSON file.
#[derive(Serialize, Deserialize)]
struct CodeContainer {
	#[serde(default, with = "sp_core::bytes")]
	code: Vec<u8>,
}

impl<G: serde::de::DeserializeOwned, E: serde::de::DeserializeOwned> ChainSpec<G, E> {
	/// Parse json content into a `ChainSpec`
	pub fn from_json_bytes(json: impl Into<Cow<'static, [u8]>>) -> Result<Self, String> {
		let json = json.into();
		let client_spec = json::from_slice(json.as_ref())
			.map_err(|e| format!("Error parsing spec file: {}", e))?;

		let code: CodeContainer = json::from_slice(json.as_ref())
			.map_err(|e| format!("Error parsing spec file: {}", e))?;

		Ok(ChainSpec { client_spec, genesis: GenesisSource::Binary(json), code: code.code })
	}

	/// Parse json file into a `ChainSpec`
	pub fn from_json_file(path: PathBuf) -> Result<Self, String> {
		// We mmap the file into memory first, as this is *a lot* faster than using
		// `serde_json::from_reader`. See https://github.com/serde-rs/json/issues/160
		let file = File::open(&path)
			.map_err(|e| format!("Error opening spec file `{}`: {}", path.display(), e))?;

		// SAFETY: `mmap` is fundamentally unsafe since technically the file can change
		//         underneath us while it is mapped; in practice it's unlikely to be a problem
		let bytes = unsafe {
			memmap2::Mmap::map(&file)
				.map_err(|e| format!("Error mmaping spec file `{}`: {}", path.display(), e))?
		};

		let client_spec =
			json::from_slice(&bytes).map_err(|e| format!("Error parsing spec file: {}", e))?;

		let code: CodeContainer =
			json::from_slice(&bytes).map_err(|e| format!("Error parsing spec file: {}", e))?;

		Ok(ChainSpec { client_spec, genesis: GenesisSource::File(path), code: code.code })
	}
}

/// Helper structure for serializing (and only serializing) the ChainSpec into JSON file. It
/// represents the layout of `ChainSpec` JSON file.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ChainSpecJsonContainer<G, E> {
	#[serde(flatten)]
	client_spec: ClientSpec<E>,
	genesis: Genesis<G>,
	#[serde(with = "sp_core::bytes", skip_serializing_if = "Vec::is_empty")]
	code: Vec<u8>,
}

impl<G: RuntimeGenesis, E: serde::Serialize + Clone + 'static> ChainSpec<G, E> {
	fn json_container(&self, raw: bool) -> Result<ChainSpecJsonContainer<G, E>, String> {
		let mut raw_genesis = match (raw, self.genesis.resolve()?) {
			(true, Genesis::RuntimeGenesisConfigPatch(patch)) => {
				let storage = RuntimeCaller::new(&self.code[..]).get_storage_for_patch(patch)?;
				RawGenesis::from(storage)
			},
			(true, Genesis::RuntimeGenesisConfig(config)) => {
				let storage = RuntimeCaller::new(&self.code[..]).get_storage_for_config(config)?;
				RawGenesis::from(storage)
			},
			#[allow(deprecated)]
			(true, Genesis::Runtime(g)) => {
				let storage = g.build_storage()?;
				RawGenesis::from(storage)
			},
			(true, Genesis::Raw(raw)) => raw,

			(_, genesis) =>
				return Ok(ChainSpecJsonContainer {
					client_spec: self.client_spec.clone(),
					genesis,
					code: self.code.clone(),
				}),
		};

		if !self.code.is_empty() {
			raw_genesis.top.insert(
				StorageKey(sp_core::storage::well_known_keys::CODE.to_vec()),
				StorageData(self.code.clone()),
			);
		}

		Ok(ChainSpecJsonContainer {
			client_spec: self.client_spec.clone(),
			genesis: Genesis::Raw(raw_genesis),
			code: vec![],
		})
	}

	/// Dump the chain specification to JSON string.
	///
	/// During conversion to `raw` format, the `ChainSpec::code` field will be removed and placed
	/// into `RawGenesis` as `genesis::top::raw::0x3a636f6465` (which is
	/// [`sp_core::storage::well_known_keys::CODE`]). If the spec is already in `raw` format, and
	/// contains `genesis::top::raw::0x3a636f6465` field it will be updated with content of `code`
	/// field (if present).
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

	fn fork_id(&self) -> Option<&str> {
		ChainSpec::fork_id(self)
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

	fn code_substitutes(&self) -> std::collections::BTreeMap<String, Vec<u8>> {
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
	use serde_json::{from_str, json, Value};
	use sp_application_crypto::Ss58Codec;
	use sp_core::storage::well_known_keys;
	use sp_keyring::AccountKeyring;
	use std::collections::VecDeque;

	#[derive(Debug, Serialize, Deserialize)]
	struct Genesis(BTreeMap<String, String>);

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

	#[derive(Debug, Serialize, Deserialize, Clone)]
	#[serde(rename_all = "camelCase")]
	struct Extension1 {
		my_property: String,
	}

	impl crate::Extension for Extension1 {
		type Forks = Option<()>;

		fn get<T: 'static>(&self) -> Option<&T> {
			None
		}

		fn get_any(&self, _: std::any::TypeId) -> &dyn std::any::Any {
			self
		}

		fn get_any_mut(&mut self, _: std::any::TypeId) -> &mut dyn std::any::Any {
			self
		}
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

	#[test]
	fn chain_spec_raw_output_should_be_deterministic() {
		let mut spec = TestSpec2::from_json_bytes(Cow::Owned(
			include_bytes!("../res/chain_spec2.json").to_vec(),
		))
		.unwrap();

		let mut storage = spec.build_storage().unwrap();

		// Add some extra data, so that storage "sorting" is tested.
		let extra_data = &[("random_key", "val"), ("r@nd0m_key", "val"), ("aaarandom_key", "val")];
		storage
			.top
			.extend(extra_data.iter().map(|(k, v)| (k.as_bytes().to_vec(), v.as_bytes().to_vec())));
		crate::ChainSpec::set_storage(&mut spec, storage);

		let json = spec.as_json(true).unwrap();

		// Check multiple times that decoding and encoding the chain spec leads always to the same
		// output.
		for _ in 0..10 {
			assert_eq!(
				json,
				TestSpec2::from_json_bytes(json.as_bytes().to_vec())
					.unwrap()
					.as_json(true)
					.unwrap()
			);
		}
	}

	macro_rules! json_path {
		[ $($x:expr),+ ] => {
			VecDeque::<String>::from([$($x),+].map(String::from))
		};
	}

	/// The `fun` will be called with the value at `path`.
	///
	/// If exists, the value at given `path` will be passed to the `fun` and the result of `fun`
	/// call will be returned. Otherwise false is returned.
	/// `path` will be modified.
	///
	/// # Examples
	/// ```
	/// use serde_json::{from_str, json, Value};
	/// let doc = json!({"a":{"b":{"c":"5"}}});
	/// let mut path = ["a", "b", "c"].map(String::from).into();
	/// assert!(json_eval_value_at_key(&doc, &mut path, &|v| { assert_eq!(v,"5"); true }));
	/// ```
	pub fn json_eval_value_at_key(
		doc: &Value,
		path: &mut VecDeque<String>,
		fun: &dyn Fn(&Value) -> bool,
	) -> bool {
		if path.len() == 1 {
			doc.as_object().map_or(false, |o| o.get(&path[0]).map_or(false, |v| fun(v)))
		} else {
			let key = path.pop_front().unwrap();
			doc.as_object().map_or(false, |o| {
				o.get(&key).map_or(false, |v| json_eval_value_at_key(v, path, fun))
			})
		}
	}

	fn json_contains_path(doc: &Value, path: &mut VecDeque<String>) -> bool {
		json_eval_value_at_key(doc, path, &|_| true)
	}

	#[test]
	// some tests for json path utils
	fn test_json_eval_value_at_key() {
		let doc = json!({"a":{"b1":"20","b":{"c":{"d":"10"}}}});

		assert!(json_eval_value_at_key(&doc, &mut json_path!["a", "b1"], &|v| { *v == "20" }));
		assert!(json_eval_value_at_key(&doc, &mut json_path!["a", "b", "c", "d"], &|v| {
			*v == "10"
		}));
		assert!(!json_eval_value_at_key(&doc, &mut json_path!["a", "c", "d"], &|_| { true }));
		assert!(!json_eval_value_at_key(&doc, &mut json_path!["d"], &|_| { true }));

		assert!(json_contains_path(&doc, &mut json_path!["a", "b1"]));
		assert!(json_contains_path(&doc, &mut json_path!["a", "b"]));
		assert!(json_contains_path(&doc, &mut json_path!["a", "b", "c"]));
		assert!(json_contains_path(&doc, &mut json_path!["a", "b", "c", "d"]));
		assert!(!json_contains_path(&doc, &mut json_path!["a", "b", "c", "d", "e"]));
		assert!(!json_contains_path(&doc, &mut json_path!["a", "b", "b1"]));
		assert!(!json_contains_path(&doc, &mut json_path!["d"]));
	}

	fn zeroize_code_key_in_json(encoded: bool, json: &str) -> Value {
		let mut json = from_str::<Value>(json).unwrap();
		let (zeroing_patch, mut path) = if encoded {
			(
				json!({"genesis":{"raw":{"top":{"0x3a636f6465":"0x0"}}}}),
				json_path!["genesis", "raw", "top", "0x3a636f6465"],
			)
		} else {
			(json!({"code":"0x0"}), json_path!["code"])
		};
		assert!(json_contains_path(&json, &mut path));
		json_patch::merge(&mut json, &zeroing_patch);
		json
	}

	#[test]
	fn generate_chain_spec_with_patch_works() {
		let output: ChainSpec<()> = ChainSpecBuilder::new()
			.with_name("TestName")
			.with_id("test_id")
			.with_extensions(Default::default())
			.with_chain_type(ChainType::Local)
			.with_code(substrate_test_runtime::wasm_binary_unwrap().into())
			.with_genesis_config_patch(json!({
				"babe": {
					"epochConfig": {
						"c": [
							7,
							10
						],
						"allowed_slots": "PrimaryAndSecondaryPlainSlots"
					}
				},
				"substrateTest": {
					"authorities": [
						AccountKeyring::Ferdie.public().to_ss58check(),
						AccountKeyring::Alice.public().to_ss58check()
					],
				}
			}))
			.build();

		let actual = output.as_json(false).unwrap();
		let actual_raw = output.as_json(true).unwrap();

		let expected =
			from_str::<Value>(include_str!("../res/substrate_test_runtime_from_patch.json"))
				.unwrap();
		let expected_raw =
			from_str::<Value>(include_str!("../res/substrate_test_runtime_from_patch__raw.json"))
				.unwrap();

		//wasm blob may change overtime so let's zero it. Also ensure it is there:
		let actual = zeroize_code_key_in_json(false, actual.as_str());
		let actual_raw = zeroize_code_key_in_json(true, actual_raw.as_str());

		assert_eq!(actual, expected);
		assert_eq!(actual_raw, expected_raw);
	}

	#[test]
	fn generate_chain_spec_with_full_config_works() {
		let j = include_str!("../../../test-utils/runtime/res/default_genesis_config.json");
		let output: ChainSpec<()> = ChainSpecBuilder::new()
			.with_name("TestName")
			.with_id("test_id")
			.with_extensions(Default::default())
			.with_chain_type(ChainType::Local)
			.with_code(substrate_test_runtime::wasm_binary_unwrap().into())
			.with_genesis_config(from_str(j).unwrap())
			.build();

		let actual = output.as_json(false).unwrap();
		let actual_raw = output.as_json(true).unwrap();

		let expected =
			from_str::<Value>(include_str!("../res/substrate_test_runtime_from_config.json"))
				.unwrap();
		let expected_raw =
			from_str::<Value>(include_str!("../res/substrate_test_runtime_from_config__raw.json"))
				.unwrap();

		//wasm blob may change overtime so let's zero it. Also ensure it is there:
		let actual = zeroize_code_key_in_json(false, actual.as_str());
		let actual_raw = zeroize_code_key_in_json(true, actual_raw.as_str());

		assert_eq!(actual, expected);
		assert_eq!(actual_raw, expected_raw);
	}

	#[test]
	fn chain_spec_as_json_fails_with_invalid_config() {
		let j =
			include_str!("../../../test-utils/runtime/res/default_genesis_config_invalid_2.json");
		let output: ChainSpec<()> = ChainSpecBuilder::new()
			.with_name("TestName")
			.with_id("test_id")
			.with_extensions(Default::default())
			.with_chain_type(ChainType::Local)
			.with_code(substrate_test_runtime::wasm_binary_unwrap().into())
			.with_genesis_config(from_str(j).unwrap())
			.build();

		assert_eq!(
			output.as_json(true),
			Err("Invalid JSON blob: unknown field `babex`, expected one of `system`, `babe`, `substrateTest`, `balances` at line 1 column 8".to_string())
		);
	}

	#[test]
	fn chain_spec_as_json_fails_with_invalid_patch() {
		let output: ChainSpec<()> = ChainSpecBuilder::new()
			.with_name("TestName")
			.with_id("test_id")
			.with_extensions(Default::default())
			.with_chain_type(ChainType::Local)
			.with_code(substrate_test_runtime::wasm_binary_unwrap().into())
			.with_genesis_config_patch(json!({
				"invalid_pallet": {},
				"substrateTest": {
					"authorities": [
						AccountKeyring::Ferdie.public().to_ss58check(),
						AccountKeyring::Alice.public().to_ss58check()
					],
				}
			}))
			.build();

		assert!(output.as_json(true).unwrap_err().contains("Invalid JSON blob: unknown field `invalid_pallet`, expected one of `system`, `babe`, `substrateTest`, `balances`"));
	}

	#[test]
	fn check_if_code_is_valid_for_raw_without_code() {
		let spec = ChainSpec::<()>::from_json_bytes(Cow::Owned(
			include_bytes!("../res/raw_no_code.json").to_vec(),
		))
		.unwrap();

		let j = from_str::<Value>(&spec.as_json(true).unwrap()).unwrap();

		assert!(json_eval_value_at_key(
			&j,
			&mut json_path!["genesis", "raw", "top", "0x3a636f6465"],
			&|v| { *v == "0x010101" }
		));
		assert!(!json_contains_path(&j, &mut json_path!["code"]));
	}

	#[test]
	fn check_if_code_is_removed_from_raw_with_encoded() {
		let spec = ChainSpec::<()>::from_json_bytes(Cow::Owned(
			include_bytes!("../res/raw_with_code.json").to_vec(),
		))
		.unwrap();

		let j = from_str::<Value>(&spec.as_json(true).unwrap()).unwrap();

		assert!(json_eval_value_at_key(
			&j,
			&mut json_path!["genesis", "raw", "top", "0x3a636f6465"],
			&|v| { *v == "0x060708" }
		));

		assert!(!json_contains_path(&j, &mut json_path!["code"]));
	}

	#[test]
	fn check_if_code_is_removed_from_raw_without_encoded() {
		let spec = ChainSpec::<()>::from_json_bytes(Cow::Owned(
			include_bytes!("../res/raw_with_code_no_encoded.json").to_vec(),
		))
		.unwrap();

		let j = from_str::<Value>(&spec.as_json(true).unwrap()).unwrap();

		assert!(json_eval_value_at_key(
			&j,
			&mut json_path!["genesis", "raw", "top", "0x3a636f6465"],
			&|v| { *v == "0x060708" }
		));

		assert!(!json_contains_path(&j, &mut json_path!["code"]));
	}

	#[test]
	fn check_code_in_assimilated_storage_for_raw_with_encoded() {
		let spec = ChainSpec::<()>::from_json_bytes(Cow::Owned(
			include_bytes!("../res/raw_with_code.json").to_vec(),
		))
		.unwrap();

		let storage = spec.build_storage().unwrap();
		assert!(storage
			.top
			.get(&well_known_keys::CODE.to_vec())
			.map(|v| *v == vec![6, 7, 8])
			.unwrap())
	}

	#[test]
	fn check_code_in_assimilated_storage_for_raw_without_encoded() {
		let spec = ChainSpec::<()>::from_json_bytes(Cow::Owned(
			include_bytes!("../res/raw_with_code_no_encoded.json").to_vec(),
		))
		.unwrap();

		let storage = spec.build_storage().unwrap();
		assert!(storage
			.top
			.get(&well_known_keys::CODE.to_vec())
			.map(|v| *v == vec![6, 7, 8])
			.unwrap())
	}

	#[test]
	fn check_code_in_assimilated_storage_for_raw_without_code() {
		let spec = ChainSpec::<()>::from_json_bytes(Cow::Owned(
			include_bytes!("../res/raw_no_code.json").to_vec(),
		))
		.unwrap();

		let storage = spec.build_storage().unwrap();
		assert!(storage
			.top
			.get(&well_known_keys::CODE.to_vec())
			.map(|v| *v == vec![1, 1, 1])
			.unwrap())
	}
}
