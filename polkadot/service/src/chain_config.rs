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
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

//! Chain configuration.

use ed25519;
use polkadot_runtime::{GenesisConfig, ConsensusConfig, CouncilConfig, DemocracyConfig,
	SessionConfig, StakingConfig};

/// Chain configuration.
pub struct ChainConfig {
	/// Genesis block confguration.
	pub genesis_config: GenesisConfig,
	/// List of bootnodes.
	pub boot_nodes: Vec<String>,
}
/// Prepare chain configuration for POC-1 testnet.
pub fn poc_1_testnet_config() -> ChainConfig {
	let initial_authorities = vec![
		hex!["82c39b31a2b79a90f8e66e7a77fdb85a4ed5517f2ae39f6a80565e8ecae85cf5"].into(),
		hex!["4de37a07567ebcbf8c64568428a835269a566723687058e017b6d69db00a77e7"].into(),
		hex!["063d7787ebca768b7445dfebe7d62cbb1625ff4dba288ea34488da266dd6dca5"].into(),
	];
	let endowed_accounts = vec![
		hex!["24d132eb1a4cbf8e46de22652019f1e07fadd5037a6a057c75dbbfd4641ba85d"].into(),
	];
	let genesis_config = GenesisConfig {
		consensus: Some(ConsensusConfig {
			code: include_bytes!("../../runtime/wasm/genesis.wasm").to_vec(),	// TODO change
			authorities: initial_authorities.clone(),
		}),
		system: None,
		session: Some(SessionConfig {
			validators: initial_authorities.clone(),
			session_length: 720,	// that's 1 hour per session.
		}),
		staking: Some(StakingConfig {
			current_era: 0,
			intentions: vec![],
			transaction_fee: 100,
			balances: endowed_accounts.iter().map(|&k|(k, 1u64 << 60)).collect(),
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
	};
	let boot_nodes = Vec::new();
	ChainConfig { genesis_config, boot_nodes }
}

/// Prepare chain configuration for local testnet.
pub fn local_testnet_config() -> ChainConfig {
	let initial_authorities = vec![
		ed25519::Pair::from_seed(b"Alice                           ").public().into(),
		ed25519::Pair::from_seed(b"Bob                             ").public().into(),
	];
	let endowed_accounts = vec![
		ed25519::Pair::from_seed(b"Alice                           ").public().into(),
		ed25519::Pair::from_seed(b"Bob                             ").public().into(),
		ed25519::Pair::from_seed(b"Charlie                         ").public().into(),
		ed25519::Pair::from_seed(b"Dave                            ").public().into(),
		ed25519::Pair::from_seed(b"Eve                             ").public().into(),
		ed25519::Pair::from_seed(b"Ferdie                          ").public().into(),
	];
	let genesis_config = GenesisConfig {
		consensus: Some(ConsensusConfig {
			code: include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/polkadot_runtime.compact.wasm").to_vec(),
			authorities: initial_authorities.clone(),
		}),
		system: None,
		session: Some(SessionConfig {
			validators: initial_authorities.clone(),
			session_length: 10,
		}),
		staking: Some(StakingConfig {
			current_era: 0,
			intentions: initial_authorities.clone(),
			transaction_fee: 1,
			balances: endowed_accounts.iter().map(|&k|(k, 1u64 << 60)).collect(),
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
			active_council: vec![],
			candidacy_bond: 10,
			voter_bond: 2,
			present_slash_per_voter: 1,
			carry_count: 4,
			presentation_duration: 10,
			approval_voting_period: 20,
			term_duration: 40,
			desired_seats: 0,
			inactive_grace_period: 1,

			cooloff_period: 75,
			voting_period: 20,
		}),
		parachains: Some(Default::default()),
	};
	let boot_nodes = Vec::new();
	ChainConfig { genesis_config, boot_nodes }
}
