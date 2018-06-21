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

use std::collections::HashMap;
use ed25519;
use serde_json;
use substrate_primitives::{AuthorityId, storage::{StorageKey, StorageData}};
use runtime_primitives::{MakeStorage, BuildStorage, StorageMap};
use polkadot_runtime::{GenesisConfig, ConsensusConfig, CouncilConfig, DemocracyConfig,
	SessionConfig, StakingConfig};
use chain_spec::ChainSpec;

enum Config {
	Local(GenesisConfig),
	Raw(&'static [u8]),
}

/// A configuration of a chain. Can be used to build a genesis block.
pub struct PresetConfig {
	genesis_config: Config,
	pub(crate) boot_nodes: Vec<String>,
}

impl BuildStorage for Config {
	fn build_storage(self) -> StorageMap {
		match self {
			Config::Local(gc) => gc.build_storage(),
			Config::Raw(json) => {
				let h: HashMap<StorageKey, StorageData> = serde_json::from_slice(json).expect("Data is from an internal source and is guaranteed to be of the correct format");
				h.into_iter().map(|(k, v)| (k.0, v.0)).collect()
			}
		}
	}
}

impl PresetConfig {
	/// Get a chain config from a spec, if it's predefined.
	pub fn from_spec(chain_spec: ChainSpec) -> Result<Self, String> {
		Ok(match chain_spec {
			ChainSpec::PoC1Testnet => Self::poc_1_testnet_config(),
			ChainSpec::Development => Self::development_config(),
			ChainSpec::LocalTestnet => Self::local_testnet_config(),
			ChainSpec::PoC2Testnet => Self::poc_2_testnet_config(),
			ChainSpec::Custom(f) => return Err(f),
		})
	}

	/// Provide the boot nodes and a storage-builder function.
	// TODO: Change return type to FnOnce as soon as Box<FnOnce> is callable or BoxFn is stablised.
	pub fn deconstruct(self) -> (MakeStorage, Vec<String>) {
		let mut gc = Some(self.genesis_config);
		let f = move || gc.take().map(BuildStorage::build_storage).unwrap_or_default();
		(Box::new(f), self.boot_nodes)
	}

	/// PoC-1 testnet config.
	fn poc_1_testnet_config() -> Self {
		let genesis_config = Config::Raw(include_bytes!("../poc-1.json"));
		let boot_nodes = vec![
			"enode://a93a29fa68d965452bf0ff8c1910f5992fe2273a72a1ee8d3a3482f68512a61974211ba32bb33f051ceb1530b8ba3527fc36224ba6b9910329025e6d9153cf50@104.211.54.233:30333".into(),
			"enode://051b18f63a316c4c5fef4631f8c550ae0adba179153588406fac3e5bbbbf534ebeda1bf475dceda27a531f6cdef3846ab6a010a269aa643a1fec7bff51af66bd@104.211.48.51:30333".into(),
			"enode://c831ec9011d2c02d2c4620fc88db6d897a40d2f88fd75f47b9e4cf3b243999acb6f01b7b7343474650b34eeb1363041a422a91f1fc3850e43482983ee15aa582@104.211.48.247:30333".into(),
		];
		PresetConfig { genesis_config, boot_nodes }
	}

	/// PoC-2 testnet config.
	fn poc_2_testnet_config() -> Self {
		let initial_authorities = vec![
			hex!["82c39b31a2b79a90f8e66e7a77fdb85a4ed5517f2ae39f6a80565e8ecae85cf5"].into(),
			hex!["4de37a07567ebcbf8c64568428a835269a566723687058e017b6d69db00a77e7"].into(),
			hex!["063d7787ebca768b7445dfebe7d62cbb1625ff4dba288ea34488da266dd6dca5"].into(),
			hex!["8101764f45778d4980dadaceee6e8af2517d3ab91ac9bec9cd1714fa5994081c"].into(),
		];
		let endowed_accounts = vec![
			hex!["f295940fa750df68a686fcf4abd4111c8a9c5a5a5a83c4c8639c451a94a7adfd"].into(),
		];
		let genesis_config = Config::Local(GenesisConfig {
			consensus: Some(ConsensusConfig {
				code: include_bytes!("../../runtime/wasm/genesis.wasm").to_vec(),	// TODO change
				authorities: initial_authorities.clone(),
			}),
			system: None,
			session: Some(SessionConfig {
				validators: initial_authorities.iter().cloned().map(Into::into).collect(),
				session_length: 720,	// that's 1 hour per session.
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
				balances: endowed_accounts.iter().map(|&k|(k, 1u128 << 60)).collect(),
				validator_count: 12,
				sessions_per_era: 24,	// 24 hours per era.
				bonding_duration: 90,	// 90 days per bond.
			}),
			democracy: Some(DemocracyConfig {
				launch_period: 120 * 24 * 14,	// 2 weeks per public referendum
				voting_period: 120 * 24 * 28,	// 4 weeks to discuss & vote on an active referendum
				minimum_deposit: 1000,	// 1000 as the minimum deposit for a referendum
			}),
			council: Some(CouncilConfig {
				active_council: vec![],
				candidacy_bond: 1000,	// 1000 to become a council candidate
				voter_bond: 100,		// 100 down to vote for a candidate
				present_slash_per_voter: 1,	// slash by 1 per voter for an invalid presentation.
				carry_count: 24,		// carry over the 24 runners-up to the next council election
				presentation_duration: 120 * 24,	// one day for presenting winners.
				approval_voting_period: 7 * 120 * 24,	// one week period between possible council elections.
				term_duration: 180 * 120 * 24,	// 180 day term duration for the council.
				desired_seats: 0, // start with no council: we'll raise this once the stake has been dispersed a bit.
				inactive_grace_period: 1,	// one addition vote should go by before an inactive voter can be reaped.

				cooloff_period: 90 * 120 * 24, // 90 day cooling off period if council member vetoes a proposal.
				voting_period: 7 * 120 * 24, // 7 day voting period for council members.
			}),
			parachains: Some(Default::default()),
		});
		let boot_nodes = vec![
			"enode://a93a29fa68d965452bf0ff8c1910f5992fe2273a72a1ee8d3a3482f68512a61974211ba32bb33f051ceb1530b8ba3527fc36224ba6b9910329025e6d9153cf50@104.211.54.233:30333".into(),
			"enode://051b18f63a316c4c5fef4631f8c550ae0adba179153588406fac3e5bbbbf534ebeda1bf475dceda27a531f6cdef3846ab6a010a269aa643a1fec7bff51af66bd@104.211.48.51:30333".into(),
			"enode://c831ec9011d2c02d2c4620fc88db6d897a40d2f88fd75f47b9e4cf3b243999acb6f01b7b7343474650b34eeb1363041a422a91f1fc3850e43482983ee15aa582@104.211.48.247:30333".into(),
		];
		PresetConfig { genesis_config, boot_nodes }
	}

	fn testnet_config(initial_authorities: Vec<AuthorityId>) -> PresetConfig {
		let endowed_accounts = vec![
			ed25519::Pair::from_seed(b"Alice                           ").public().0.into(),
			ed25519::Pair::from_seed(b"Bob                             ").public().0.into(),
			ed25519::Pair::from_seed(b"Charlie                         ").public().0.into(),
			ed25519::Pair::from_seed(b"Dave                            ").public().0.into(),
			ed25519::Pair::from_seed(b"Eve                             ").public().0.into(),
			ed25519::Pair::from_seed(b"Ferdie                          ").public().0.into(),
		];
		let genesis_config = Config::Local(GenesisConfig {
			consensus: Some(ConsensusConfig {
				code: include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/polkadot_runtime.compact.wasm").to_vec(),
				authorities: initial_authorities.clone(),
			}),
			system: None,
			session: Some(SessionConfig {
				validators: initial_authorities.iter().cloned().map(Into::into).collect(),
				session_length: 10,
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
			}),
			democracy: Some(DemocracyConfig {
				launch_period: 9,
				voting_period: 18,
				minimum_deposit: 10,
			}),
			council: Some(CouncilConfig {
				active_council: endowed_accounts.iter().filter(|a| initial_authorities.iter().find(|&b| &a.0 == b).is_none()).map(|a| (a.clone(), 1000000)).collect(),
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
		});
		let boot_nodes = Vec::new();
		PresetConfig { genesis_config, boot_nodes }
	}

	/// Development config (single validator Alice)
	fn development_config() -> Self {
		Self::testnet_config(vec![
			ed25519::Pair::from_seed(b"Alice                           ").public().into(),
		])
	}

	/// Local testnet config (multivalidator Alice + Bob)
	fn local_testnet_config() -> Self {
		Self::testnet_config(vec![
			ed25519::Pair::from_seed(b"Alice                           ").public().into(),
			ed25519::Pair::from_seed(b"Bob                             ").public().into(),
		])
	}
}
