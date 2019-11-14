// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Genesis Configuration.

use crate::keyring::*;
use keyring::{Ed25519Keyring, Sr25519Keyring};
use node_runtime::{
	GenesisConfig, BalancesConfig, SessionConfig, StakingConfig, SystemConfig,
	GrandpaConfig, IndicesConfig, ContractsConfig, WASM_BINARY,
};
use node_runtime::constants::currency::*;
use primitives::ChangesTrieConfiguration;
use sr_primitives::Perbill;


/// Create genesis runtime configuration for tests.
pub fn config(support_changes_trie: bool, code: Option<&[u8]>) -> GenesisConfig {
	GenesisConfig {
		system: Some(SystemConfig {
			changes_trie_config: if support_changes_trie { Some(ChangesTrieConfiguration {
				digest_interval: 2,
				digest_levels: 2,
			}) } else { None },
			code: code.map(|x| x.to_vec()).unwrap_or_else(|| WASM_BINARY.to_vec()),
		}),
		indices: Some(IndicesConfig {
			ids: vec![alice(), bob(), charlie(), dave(), eve(), ferdie()],
		}),
		balances: Some(BalancesConfig {
			balances: vec![
				(alice(), 111 * DOLLARS),
				(bob(), 100 * DOLLARS),
				(charlie(), 100_000_000 * DOLLARS),
				(dave(), 111 * DOLLARS),
				(eve(), 101 * DOLLARS),
				(ferdie(), 100 * DOLLARS),
			],
			vesting: vec![],
		}),
		session: Some(SessionConfig {
			keys: vec![
				(alice(), to_session_keys(
					&Ed25519Keyring::Alice,
					&Sr25519Keyring::Alice,
				)),
				(bob(), to_session_keys(
					&Ed25519Keyring::Bob,
					&Sr25519Keyring::Bob,
				)),
				(charlie(), to_session_keys(
					&Ed25519Keyring::Charlie,
					&Sr25519Keyring::Charlie,
				)),
			]
		}),
		staking: Some(StakingConfig {
			current_era: 0,
			stakers: vec![
				(dave(), alice(), 111 * DOLLARS, staking::StakerStatus::Validator),
				(eve(), bob(), 100 * DOLLARS, staking::StakerStatus::Validator),
				(ferdie(), charlie(), 100 * DOLLARS, staking::StakerStatus::Validator)
			],
			validator_count: 3,
			minimum_validator_count: 0,
			slash_reward_fraction: Perbill::from_percent(10),
			invulnerables: vec![alice(), bob(), charlie()],
			.. Default::default()
		}),
		contracts: Some(ContractsConfig {
			current_schedule: Default::default(),
			gas_price: 1 * MILLICENTS,
		}),
		babe: Some(Default::default()),
		grandpa: Some(GrandpaConfig {
			authorities: vec![],
		}),
		im_online: Some(Default::default()),
		authority_discovery: Some(Default::default()),
		democracy: Some(Default::default()),
		collective_Instance1: Some(Default::default()),
		collective_Instance2: Some(Default::default()),
		membership_Instance1: Some(Default::default()),
		sudo: Some(Default::default()),
		treasury: Some(Default::default()),
	}
}
