// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Polkadot chain configurations.

use ed25519;
use std::collections::HashMap;
use std::fs::File;
use std::path::PathBuf;
use primitives::{AuthorityId, storage::{StorageKey, StorageData}};
use runtime_primitives::{BuildStorage, StorageMap};
use polkadot_runtime::{GenesisConfig, ConsensusConfig, CouncilConfig, DemocracyConfig,
	SessionConfig, StakingConfig, TimestampConfig};
use serde_json as json;

enum GenesisSource {
	File(PathBuf),
	Embedded(&'static [u8]),
	Factory(fn() -> Genesis),
}

impl GenesisSource {
	fn resolve(&self) -> Result<Genesis, String> {
		#[derive(Serialize, Deserialize)]
		struct GenesisContainer {
			genesis: Genesis,
		}

		match *self {
			GenesisSource::File(ref path) => {
				let file = File::open(path).map_err(|e| format!("Error opening spec file: {}", e))?;
				let genesis: GenesisContainer = json::from_reader(file).map_err(|e| format!("Error parsing spec file: {}", e))?;
				Ok(genesis.genesis)
			},
			GenesisSource::Embedded(buf) => {
				let genesis: GenesisContainer = json::from_reader(buf).map_err(|e| format!("Error parsing embedded file: {}", e))?;
				Ok(genesis.genesis)
			},
			GenesisSource::Factory(f) => Ok(f()),
		}
	}
}

impl<'a> BuildStorage for &'a ChainSpec {
	fn build_storage(self) -> Result<StorageMap, String> {
		match self.genesis.resolve()? {
			Genesis::Runtime(gc) => gc.build_storage(),
			Genesis::Raw(map) => Ok(map.into_iter().map(|(k, v)| (k.0, v.0)).collect()),
		}
	}
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
enum Genesis {
	Runtime(GenesisConfig),
	Raw(HashMap<StorageKey, StorageData>),
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
struct ChainSpecFile {
	pub name: String,
	pub boot_nodes: Vec<String>,
}

/// A configuration of a chain. Can be used to build a genesis block.
pub struct ChainSpec {
	spec: ChainSpecFile,
	genesis: GenesisSource,
}

impl ChainSpec {
	pub fn boot_nodes(&self) -> &[String] {
		&self.spec.boot_nodes
	}

	pub fn name(&self) -> &str {
		&self.spec.name
	}

	/// Parse json content into a `ChainSpec`
	pub fn from_embedded(json: &'static [u8]) -> Result<Self, String> {
		let spec = json::from_slice(json).map_err(|e| format!("Error parsing spec file: {}", e))?;
		Ok(ChainSpec {
			spec,
			genesis: GenesisSource::Embedded(json),
		})
	}

	/// Parse json file into a `ChainSpec`
	pub fn from_json_file(path: PathBuf) -> Result<Self, String> {
		let file = File::open(&path).map_err(|e| format!("Error opening spec file: {}", e))?;
		let spec = json::from_reader(file).map_err(|e| format!("Error parsing spec file: {}", e))?;
		Ok(ChainSpec {
			spec,
			genesis: GenesisSource::File(path),
		})
	}

	/// Dump to json string.
	pub fn to_json(self, raw: bool) -> Result<String, String> {
		let genesis = match (raw, self.genesis.resolve()?) {
			(true, Genesis::Runtime(g)) => {
				let storage = g.build_storage()?.into_iter()
					.map(|(k, v)| (StorageKey(k), StorageData(v)))
					.collect();

				Genesis::Raw(storage)
			},
			(_, genesis) => genesis,
		};
		let mut spec = json::to_value(self.spec).map_err(|e| format!("Error generating spec json: {}", e))?;
		{
			let map = spec.as_object_mut().expect("spec is an object");
			map.insert("genesis".to_owned(), json::to_value(genesis).map_err(|e| format!("Error generating genesis json: {}", e))?);
		}
		json::to_string_pretty(&spec).map_err(|e| format!("Error generating spec json: {}", e))
	}

	pub fn poc_1_testnet_config() -> Result<Self, String> {
		Self::from_embedded(include_bytes!("../res/poc-1.json"))
	}

	fn poc_2_testnet_config_genesis() -> Genesis {
		let initial_authorities = vec![
			hex!["82c39b31a2b79a90f8e66e7a77fdb85a4ed5517f2ae39f6a80565e8ecae85cf5"].into(),
			hex!["4de37a07567ebcbf8c64568428a835269a566723687058e017b6d69db00a77e7"].into(),
			hex!["063d7787ebca768b7445dfebe7d62cbb1625ff4dba288ea34488da266dd6dca5"].into(),
			hex!["8101764f45778d4980dadaceee6e8af2517d3ab91ac9bec9cd1714fa5994081c"].into(),
		];
		let endowed_accounts = vec![
			hex!["f295940fa750df68a686fcf4abd4111c8a9c5a5a5a83c4c8639c451a94a7adfd"].into(),
		];
		Genesis::Runtime(GenesisConfig {
			consensus: Some(ConsensusConfig {
				code: include_bytes!("../../runtime/wasm/genesis.wasm").to_vec(),	// TODO change
				authorities: initial_authorities.clone(),
			}),
			system: None,
			session: Some(SessionConfig {
				validators: initial_authorities.iter().cloned().map(Into::into).collect(),
				session_length: 60,	// that's 5 minutes per session.
				broken_percent_late: 50,
			}),
			staking: Some(StakingConfig {
				current_era: 0,
				intentions: initial_authorities.iter().cloned().map(Into::into).collect(),
				transaction_base_fee: 100,
				transaction_byte_fee: 1,
				existential_deposit: 500,
				transfer_fee: 0,
				creation_fee: 0,
				contract_fee: 0,
				reclaim_rebate: 0,
				early_era_slash: 10000,
				session_reward: 100,
				balances: endowed_accounts.iter().map(|&k|(k, 1u128 << 60)).collect(),
				validator_count: 12,
				sessions_per_era: 12,	// 1 hour per era
				bonding_duration: 24,	// 1 day per bond.
			}),
			democracy: Some(DemocracyConfig {
				launch_period: 12 * 60 * 24,	// 1 day per public referendum
				voting_period: 12 * 60 * 24 * 3,	// 3 days to discuss & vote on an active referendum
				minimum_deposit: 5000,	// 12000 as the minimum deposit for a referendum
			}),
			council: Some(CouncilConfig {
				active_council: vec![],
				candidacy_bond: 5000,	// 5000 to become a council candidate
				voter_bond: 1000,		// 1000 down to vote for a candidate
				present_slash_per_voter: 1,	// slash by 1 per voter for an invalid presentation.
				carry_count: 6,		// carry over the 6 runners-up to the next council election
				presentation_duration: 12 * 60 * 24,	// one day for presenting winners.
				approval_voting_period: 12 * 60 * 24 * 2,	// two days period between possible council elections.
				term_duration: 12 * 60 * 24 * 24,	// 24 day term duration for the council.
				desired_seats: 0, // start with no council: we'll raise this once the stake has been dispersed a bit.
				inactive_grace_period: 1,	// one addition vote should go by before an inactive voter can be reaped.

				cooloff_period: 12 * 60 * 24 * 4, // 4 day cooling off period if council member vetoes a proposal.
				voting_period: 12 * 60 * 24, // 1 day voting period for council members.
			}),
			parachains: Some(Default::default()),
			timestamp: Some(TimestampConfig {
				period: 5,					// 5 second block time.
			}),
		})
	}
	/// PoC-2 testnet config.
	pub fn poc_2_testnet_config() -> Self {
		let boot_nodes = vec![
			"enode://a93a29fa68d965452bf0ff8c1910f5992fe2273a72a1ee8d3a3482f68512a61974211ba32bb33f051ceb1530b8ba3527fc36224ba6b9910329025e6d9153cf50@104.211.54.233:30333".into(),
			"enode://051b18f63a316c4c5fef4631f8c550ae0adba179153588406fac3e5bbbbf534ebeda1bf475dceda27a531f6cdef3846ab6a010a269aa643a1fec7bff51af66bd@104.211.48.51:30333".into(),
			"enode://c831ec9011d2c02d2c4620fc88db6d897a40d2f88fd75f47b9e4cf3b243999acb6f01b7b7343474650b34eeb1363041a422a91f1fc3850e43482983ee15aa582@104.211.48.247:30333".into(),
		];
		ChainSpec {
			spec: ChainSpecFile { name: "PoC-2 Testnet".to_owned(), boot_nodes },
			genesis: GenesisSource::Factory(Self::poc_2_testnet_config_genesis),
		}
	}

	fn testnet_genesis(initial_authorities: Vec<AuthorityId>) -> Genesis {
		let endowed_accounts = vec![
			ed25519::Pair::from_seed(b"Alice                           ").public().0.into(),
			ed25519::Pair::from_seed(b"Bob                             ").public().0.into(),
			ed25519::Pair::from_seed(b"Charlie                         ").public().0.into(),
			ed25519::Pair::from_seed(b"Dave                            ").public().0.into(),
			ed25519::Pair::from_seed(b"Eve                             ").public().0.into(),
			ed25519::Pair::from_seed(b"Ferdie                          ").public().0.into(),
		];
		Genesis::Runtime(GenesisConfig {
			consensus: Some(ConsensusConfig {
				code: include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/polkadot_runtime.compact.wasm").to_vec(),
				authorities: initial_authorities.clone(),
			}),
			system: None,
			session: Some(SessionConfig {
				validators: initial_authorities.iter().cloned().map(Into::into).collect(),
				session_length: 10,
				broken_percent_late: 30,
			}),
			staking: Some(StakingConfig {
				current_era: 0,
				intentions: initial_authorities.iter().cloned().map(Into::into).collect(),
				transaction_base_fee: 1,
				transaction_byte_fee: 0,
				existential_deposit: 500,
				transfer_fee: 0,
				creation_fee: 0,
				contract_fee: 0,
				reclaim_rebate: 0,
				balances: endowed_accounts.iter().map(|&k|(k, (1u128 << 60))).collect(),
				validator_count: 2,
				sessions_per_era: 5,
				bonding_duration: 2,
				early_era_slash: 0,
				session_reward: 0,
			}),
			democracy: Some(DemocracyConfig {
				launch_period: 9,
				voting_period: 18,
				minimum_deposit: 10,
			}),
			council: Some(CouncilConfig {
				active_council: endowed_accounts.iter().filter(|a| initial_authorities.iter().find(|&b| a.0 == b.0).is_none()).map(|a| (a.clone(), 1000000)).collect(),
				candidacy_bond: 10,
				voter_bond: 2,
				present_slash_per_voter: 1,
				carry_count: 4,
				presentation_duration: 10,
				approval_voting_period: 20,
				term_duration: 1000000,
				desired_seats: (endowed_accounts.len() - initial_authorities.len()) as u32,
				inactive_grace_period: 1,

				cooloff_period: 75,
				voting_period: 20,
			}),
			parachains: Some(Default::default()),
			timestamp: Some(TimestampConfig {
				period: 5,					// 5 second block time.
			}),
		})
	}

	fn development_config_genesis() -> Genesis {
		Self::testnet_genesis(vec![
			ed25519::Pair::from_seed(b"Alice                           ").public().into(),
		])
	}

	/// Development config (single validator Alice)
	pub fn development_config() -> Self {
		ChainSpec {
			spec: ChainSpecFile { name: "Development".to_owned(), boot_nodes: vec![] },
			genesis: GenesisSource::Factory(Self::development_config_genesis),
		}
	}

	fn local_testnet_genesis() -> Genesis {
		Self::testnet_genesis(vec![
			ed25519::Pair::from_seed(b"Alice                           ").public().into(),
			ed25519::Pair::from_seed(b"Bob                             ").public().into(),
		])
	}

	/// Local testnet config (multivalidator Alice + Bob)
	pub fn local_testnet_config() -> Self {
		ChainSpec {
			spec: ChainSpecFile { name: "Local Testnet".to_owned(), boot_nodes: vec![] },
			genesis: GenesisSource::Factory(Self::local_testnet_genesis),
		}
	}
}
