// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Substrate chain configurations.

use std::borrow::Cow;
use std::collections::HashMap;
use std::fs::File;
use std::path::PathBuf;
use std::sync::Arc;
use serde::{Serialize, Deserialize};
use sp_core::storage::{StorageKey, StorageData, ChildInfo, Storage, StorageChild};
use sp_runtime::BuildStorage;
use serde_json as json;
use crate::RuntimeGenesis;
use crate::extension::GetExtension;
use sc_network::Multiaddr;
use sc_telemetry::TelemetryEndpoints;

enum GenesisSource<G> {
	File(PathBuf),
	Binary(Cow<'static, [u8]>),
	Factory(Arc<dyn Fn() -> G + Send + Sync>),
}

impl<G> Clone for GenesisSource<G> {
	fn clone(&self) -> Self {
		match *self {
			GenesisSource::File(ref path) => GenesisSource::File(path.clone()),
			GenesisSource::Binary(ref d) => GenesisSource::Binary(d.clone()),
			GenesisSource::Factory(ref f) => GenesisSource::Factory(f.clone()),
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
			GenesisSource::File(path) => {
				let file = File::open(path)
					.map_err(|e| format!("Error opening spec file: {}", e))?;
				let genesis: GenesisContainer<G> = json::from_reader(file)
					.map_err(|e| format!("Error parsing spec file: {}", e))?;
				Ok(genesis.genesis)
			},
			GenesisSource::Binary(buf) => {
				let genesis: GenesisContainer<G> = json::from_reader(buf.as_ref())
					.map_err(|e| format!("Error parsing embedded file: {}", e))?;
				Ok(genesis.genesis)
			},
			GenesisSource::Factory(f) => Ok(Genesis::Runtime(f())),
		}
	}
}

impl<G: RuntimeGenesis, E> BuildStorage for ChainSpec<G, E> {
	fn build_storage(&self) -> Result<Storage, String> {
		match self.genesis.resolve()? {
			Genesis::Runtime(gc) => gc.build_storage(),
			Genesis::Raw(RawGenesis { top: map, children: children_map }) => Ok(Storage {
				top: map.into_iter().map(|(k, v)| (k.0, v.0)).collect(),
				children: children_map.into_iter().map(|(sk, child_content)| {
					let child_info = ChildInfo::resolve_child_info(
						child_content.child_type,
						child_content.child_info.as_slice(),
					).expect("chain spec contains correct content").to_owned();
					(
						sk.0,
						StorageChild {
							data: child_content.data.into_iter().map(|(k, v)| (k.0, v.0)).collect(),
							child_info,
						},
					)
				}).collect(),
			}),
		}
	}

	fn assimilate_storage(
		&self,
		_: &mut Storage,
	) -> Result<(), String> {
		Err("`assimilate_storage` not implemented for `ChainSpec`.".into())
	}
}

type GenesisStorage = HashMap<StorageKey, StorageData>;

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
struct ChildRawStorage {
	data: GenesisStorage,
	child_info: Vec<u8>,
	child_type: u32,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
/// Storage content for genesis block.
struct RawGenesis {
	top: GenesisStorage,
	children: HashMap<StorageKey, ChildRawStorage>,
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
	boot_nodes: Vec<String>,
	telemetry_endpoints: Option<TelemetryEndpoints>,
	protocol_id: Option<String>,
	properties: Option<Properties>,
	#[serde(flatten)]
	extensions: E,
	// Never used, left only for backward compatibility.
	consensus_engine: (),
	#[serde(skip_serializing)]
	genesis: serde::de::IgnoredAny,
}

/// Arbitrary properties defined in chain spec as a JSON object
pub type Properties = json::map::Map<String, json::Value>;

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
		ChainSpec {
			client_spec: self.client_spec.clone(),
			genesis: self.genesis.clone(),
		}
	}
}

impl<G, E> ChainSpec<G, E> {
	/// A list of bootnode addresses.
	pub fn boot_nodes(&self) -> &[String] {
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
	pub fn add_boot_node(&mut self, addr: Multiaddr) {
		self.client_spec.boot_nodes.push(addr.to_string())
	}

	/// Returns a reference to defined chain spec extensions.
	pub fn extensions(&self) -> &E {
		&self.client_spec.extensions
	}

	/// Create hardcoded spec.
	pub fn from_genesis<F: Fn() -> G + 'static + Send + Sync>(
		name: &str,
		id: &str,
		constructor: F,
		boot_nodes: Vec<String>,
		telemetry_endpoints: Option<TelemetryEndpoints>,
		protocol_id: Option<&str>,
		properties: Option<Properties>,
		extensions: E,
	) -> Self {
		let client_spec = ClientSpec {
			name: name.to_owned(),
			id: id.to_owned(),
			boot_nodes,
			telemetry_endpoints,
			protocol_id: protocol_id.map(str::to_owned),
			properties,
			extensions,
			consensus_engine: (),
			genesis: Default::default(),
		};

		ChainSpec {
			client_spec,
			genesis: GenesisSource::Factory(Arc::new(constructor)),
		}
	}
}

impl<G, E: serde::de::DeserializeOwned> ChainSpec<G, E> {
	/// Parse json content into a `ChainSpec`
	pub fn from_json_bytes(json: impl Into<Cow<'static, [u8]>>) -> Result<Self, String> {
		let json = json.into();
		let client_spec = json::from_slice(json.as_ref())
			.map_err(|e| format!("Error parsing spec file: {}", e))?;
		Ok(ChainSpec {
			client_spec,
			genesis: GenesisSource::Binary(json),
		})
	}

	/// Parse json file into a `ChainSpec`
	pub fn from_json_file(path: PathBuf) -> Result<Self, String> {
		let file = File::open(&path)
			.map_err(|e| format!("Error opening spec file: {}", e))?;
		let client_spec = json::from_reader(file)
			.map_err(|e| format!("Error parsing spec file: {}", e))?;
		Ok(ChainSpec {
			client_spec,
			genesis: GenesisSource::File(path),
		})
	}
}

impl<G: RuntimeGenesis, E: serde::Serialize + Clone> ChainSpec<G, E> {
	/// Dump to json string.
	pub fn as_json(&self, raw: bool) -> Result<String, String> {
		#[derive(Serialize, Deserialize)]
		struct Container<G, E> {
			#[serde(flatten)]
			client_spec: ClientSpec<E>,
			genesis: Genesis<G>,

		};
		let genesis = match (raw, self.genesis.resolve()?) {
			(true, Genesis::Runtime(g)) => {
				let storage = g.build_storage()?;
				let top = storage.top.into_iter()
					.map(|(k, v)| (StorageKey(k), StorageData(v)))
					.collect();
				let children = storage.children.into_iter()
					.map(|(sk, child)| {
						let info = child.child_info.as_ref();
						let (info, ci_type) = info.info();
						(
							StorageKey(sk),
							ChildRawStorage {
								data: child.data.into_iter()
									.map(|(k, v)| (StorageKey(k), StorageData(v)))
									.collect(),
								child_info: info.to_vec(),
								child_type: ci_type,
							},
					)})
					.collect();

				Genesis::Raw(RawGenesis { top, children })
			},
			(_, genesis) => genesis,
		};
		let container = Container {
			client_spec: self.client_spec.clone(),
			genesis,
		};
		json::to_string_pretty(&container)
			.map_err(|e| format!("Error generating spec json: {}", e))
	}
}

impl<G, E> crate::ChainSpec for ChainSpec<G, E>
where
	G: RuntimeGenesis,
	E: GetExtension + serde::Serialize + Clone,
{
	fn boot_nodes(&self) -> &[String] {
		ChainSpec::boot_nodes(self)
	}

	fn name(&self) -> &str {
		ChainSpec::name(self)
	}

	fn id(&self) -> &str {
		ChainSpec::id(self)
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

	fn add_boot_node(&mut self, addr: Multiaddr) {
		ChainSpec::add_boot_node(self, addr)
	}

	fn extensions(&self) -> &dyn GetExtension {
		ChainSpec::extensions(self) as &dyn GetExtension
	}

	fn as_json(&self, raw: bool) -> Result<String, String> {
		ChainSpec::as_json(self, raw)
	}

	fn as_storage_builder(&self) -> &dyn BuildStorage {
		self
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[derive(Debug, Serialize, Deserialize)]
	struct Genesis(HashMap<String, String>);

	impl BuildStorage for Genesis {
		fn assimilate_storage(
			&self,
			storage: &mut Storage,
		) -> Result<(), String> {
			storage.top.extend(
				self.0.iter().map(|(a, b)| (a.clone().into_bytes(), b.clone().into_bytes()))
			);
			Ok(())
		}
	}

	type TestSpec = ChainSpec<Genesis>;

	#[test]
	fn should_deserialize_example_chain_spec() {
		let spec1 = TestSpec::from_json_bytes(Cow::Owned(
			include_bytes!("../res/chain_spec.json").to_vec()
		)).unwrap();
		let spec2 = TestSpec::from_json_file(
			PathBuf::from("./res/chain_spec.json")
		).unwrap();

		assert_eq!(spec1.as_json(false), spec2.as_json(false));
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
			include_bytes!("../res/chain_spec2.json").to_vec()
		)).unwrap();

		assert_eq!(spec.extensions().my_property, "Test Extension");
	}
}
