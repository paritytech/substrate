// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use std::rc::Rc;
use serde::{Serialize, Deserialize};
use primitives::storage::{StorageKey, StorageData};
use sp_runtime::{BuildStorage, StorageOverlay, ChildrenStorageOverlay};
use serde_json as json;
use crate::RuntimeGenesis;
use network::Multiaddr;
use tel::TelemetryEndpoints;

enum GenesisSource<G> {
	File(PathBuf),
	Binary(Cow<'static, [u8]>),
	Factory(Rc<dyn Fn() -> G>),
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

impl<'a, G: RuntimeGenesis, E> BuildStorage for &'a ChainSpec<G, E> {
	fn build_storage(&self) -> Result<(StorageOverlay, ChildrenStorageOverlay), String> {
		match self.genesis.resolve()? {
			Genesis::Runtime(gc) => gc.build_storage(),
			Genesis::Raw(map, children_map) => Ok((
				map.into_iter().map(|(k, v)| (k.0, v.0)).collect(),
				children_map.into_iter().map(|(sk, map)| (
					sk.0,
					map.into_iter().map(|(k, v)| (k.0, v.0)).collect(),
				)).collect(),
			)),
		}
	}

	fn assimilate_storage(
		&self,
		_: &mut (StorageOverlay, ChildrenStorageOverlay)
	) -> Result<(), String> {
		Err("`assimilate_storage` not implemented for `ChainSpec`.".into())
	}
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
enum Genesis<G> {
	Runtime(G),
	Raw(
		HashMap<StorageKey, StorageData>,
		HashMap<StorageKey, HashMap<StorageKey, StorageData>>,
	),
}

#[derive(Serialize, Deserialize, Clone, Debug)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
struct ChainSpecFile<E> {
	pub name: String,
	pub id: String,
	pub boot_nodes: Vec<String>,
	pub telemetry_endpoints: Option<TelemetryEndpoints>,
	pub protocol_id: Option<String>,
	pub properties: Option<Properties>,
	#[serde(flatten)]
	pub extensions: E,
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
	spec: ChainSpecFile<E>,
	genesis: GenesisSource<G>,
}

impl<G, E: Clone> Clone for ChainSpec<G, E> {
	fn clone(&self) -> Self {
		ChainSpec {
			spec: self.spec.clone(),
			genesis: self.genesis.clone(),
		}
	}
}

impl<G, E> ChainSpec<G, E> {
	/// A list of bootnode addresses.
	pub fn boot_nodes(&self) -> &[String] {
		&self.spec.boot_nodes
	}

	/// Spec name.
	pub fn name(&self) -> &str {
		&self.spec.name
	}

	/// Spec id.
	pub fn id(&self) -> &str {
		&self.spec.id
	}

	/// Telemetry endpoints (if any)
	pub fn telemetry_endpoints(&self) -> &Option<TelemetryEndpoints> {
		&self.spec.telemetry_endpoints
	}

	/// Network protocol id.
	pub fn protocol_id(&self) -> Option<&str> {
		self.spec.protocol_id.as_ref().map(String::as_str)
	}

	/// Additional loosly-typed properties of the chain.
	///
	/// Returns an empty JSON object if 'properties' not defined in config
	pub fn properties(&self) -> Properties {
		self.spec.properties.as_ref().unwrap_or(&json::map::Map::new()).clone()
	}

	/// Add a bootnode to the list.
	pub fn add_boot_node(&mut self, addr: Multiaddr) {
		self.spec.boot_nodes.push(addr.to_string())
	}

	/// Returns a reference to defined chain spec extensions.
	pub fn extensions(&self) -> &E {
		&self.spec.extensions
	}

	/// Create hardcoded spec.
	pub fn from_genesis<F: Fn() -> G + 'static>(
		name: &str,
		id: &str,
		constructor: F,
		boot_nodes: Vec<String>,
		telemetry_endpoints: Option<TelemetryEndpoints>,
		protocol_id: Option<&str>,
		properties: Option<Properties>,
		extensions: E,
	) -> Self {
		let spec = ChainSpecFile {
			name: name.to_owned(),
			id: id.to_owned(),
			boot_nodes: boot_nodes,
			telemetry_endpoints,
			protocol_id: protocol_id.map(str::to_owned),
			properties,
			extensions,
			consensus_engine: (),
			genesis: Default::default(),
		};

		ChainSpec {
			spec,
			genesis: GenesisSource::Factory(Rc::new(constructor)),
		}
	}
}

impl<G, E: serde::de::DeserializeOwned> ChainSpec<G, E> {
	/// Parse json content into a `ChainSpec`
	pub fn from_json_bytes(json: impl Into<Cow<'static, [u8]>>) -> Result<Self, String> {
		let json = json.into();
		let spec = json::from_slice(json.as_ref())
			.map_err(|e| format!("Error parsing spec file: {}", e))?;
		Ok(ChainSpec {
			spec,
			genesis: GenesisSource::Binary(json),
		})
	}

	/// Parse json file into a `ChainSpec`
	pub fn from_json_file(path: PathBuf) -> Result<Self, String> {
		let file = File::open(&path)
			.map_err(|e| format!("Error opening spec file: {}", e))?;
		let spec = json::from_reader(file)
			.map_err(|e| format!("Error parsing spec file: {}", e))?;
		Ok(ChainSpec {
			spec,
			genesis: GenesisSource::File(path),
		})
	}
}

impl<G: RuntimeGenesis, E: serde::Serialize> ChainSpec<G, E> {
	/// Dump to json string.
	pub fn to_json(self, raw: bool) -> Result<String, String> {
		#[derive(Serialize, Deserialize)]
		struct Container<G, E> {
			#[serde(flatten)]
			spec: ChainSpecFile<E>,
			genesis: Genesis<G>,

		};
		let genesis = match (raw, self.genesis.resolve()?) {
			(true, Genesis::Runtime(g)) => {
				let storage = g.build_storage()?;
				let top = storage.0.into_iter()
					.map(|(k, v)| (StorageKey(k), StorageData(v)))
					.collect();
				let children = storage.1.into_iter()
					.map(|(sk, child)| (
							StorageKey(sk),
							child.into_iter()
								.map(|(k, v)| (StorageKey(k), StorageData(v)))
								.collect(),
					))
					.collect();

				Genesis::Raw(top, children)
			},
			(_, genesis) => genesis,
		};
		let spec = Container {
			spec: self.spec,
			genesis,
		};
		json::to_string_pretty(&spec)
			.map_err(|e| format!("Error generating spec json: {}", e))
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
			storage: &mut (StorageOverlay, ChildrenStorageOverlay),
		) -> Result<(), String> {
			storage.0.extend(
				self.0.iter().map(|(a, b)| (a.clone().into_bytes(), b.clone().into_bytes()))
			);
			Ok(())
		}
	}

	type TestSpec = ChainSpec<Genesis>;

	#[test]
	fn should_deserailize_example_chain_spec() {
		let spec1 = TestSpec::from_json_bytes(Cow::Owned(
			include_bytes!("../res/chain_spec.json").to_vec()
		)).unwrap();
		let spec2 = TestSpec::from_json_file(
			PathBuf::from("./res/chain_spec.json")
		).unwrap();

		assert_eq!(spec1.to_json(false), spec2.to_json(false));
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
