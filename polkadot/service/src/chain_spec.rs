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
use primitives::AuthorityId;
use polkadot_runtime::{GenesisConfig, ConsensusConfig, CouncilConfig, DemocracyConfig,
	SessionConfig, StakingConfig, TimestampConfig};
use service::ChainSpec;

const STAGING_TELEMETRY_URL: &str = "wss://telemetry.polkadot.io/submit/";

pub fn poc_1_testnet_config() -> Result<ChainSpec<GenesisConfig>, String> {
	ChainSpec::from_embedded(include_bytes!("../res/krummelanke.json"))
}

fn staging_testnet_config_genesis() -> GenesisConfig {
	let initial_authorities = vec![
		hex!["82c39b31a2b79a90f8e66e7a77fdb85a4ed5517f2ae39f6a80565e8ecae85cf5"].into(),
		hex!["4de37a07567ebcbf8c64568428a835269a566723687058e017b6d69db00a77e7"].into(),
		hex!["063d7787ebca768b7445dfebe7d62cbb1625ff4dba288ea34488da266dd6dca5"].into(),
		hex!["8101764f45778d4980dadaceee6e8af2517d3ab91ac9bec9cd1714fa5994081c"].into(),
	];
	let endowed_accounts = vec![
		hex!["f295940fa750df68a686fcf4abd4111c8a9c5a5a5a83c4c8639c451a94a7adfd"].into(),
	];
	GenesisConfig {
		consensus: Some(ConsensusConfig {
			code: include_bytes!("../../runtime/wasm/target/wasm32-unknown-unknown/release/polkadot_runtime.compact.wasm").to_vec(),	// TODO change
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
	}
}

/// Staging testnet config.
pub fn staging_testnet_config() -> ChainSpec<GenesisConfig> {
	let boot_nodes = vec![];
	ChainSpec::from_genesis(
		"Staging Testnet",
		"staging_testnet",
		staging_testnet_config_genesis,
		boot_nodes,
		Some(STAGING_TELEMETRY_URL.into()),
	)
}

fn testnet_genesis(initial_authorities: Vec<AuthorityId>) -> GenesisConfig {
	let endowed_accounts = vec![
		ed25519::Pair::from_seed(b"Alice                           ").public().0.into(),
		ed25519::Pair::from_seed(b"Bob                             ").public().0.into(),
		ed25519::Pair::from_seed(b"Charlie                         ").public().0.into(),
		ed25519::Pair::from_seed(b"Dave                            ").public().0.into(),
		ed25519::Pair::from_seed(b"Eve                             ").public().0.into(),
		ed25519::Pair::from_seed(b"Ferdie                          ").public().0.into(),
	];
	GenesisConfig {
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
	}
}

fn development_config_genesis() -> GenesisConfig {
	testnet_genesis(vec![
		ed25519::Pair::from_seed(b"Alice                           ").public().into(),
	])
}

/// Development config (single validator Alice)
pub fn development_config() -> ChainSpec<GenesisConfig> {
	ChainSpec::from_genesis("Development", "development", development_config_genesis, vec![], None)
}

fn local_testnet_genesis() -> GenesisConfig {
	testnet_genesis(vec![
		ed25519::Pair::from_seed(b"Alice                           ").public().into(),
		ed25519::Pair::from_seed(b"Bob                             ").public().into(),
	])
}

/// Local testnet config (multivalidator Alice + Bob)
pub fn local_testnet_config() -> ChainSpec<GenesisConfig> {
	ChainSpec::from_genesis("Local Testnet", "local_testnet", local_testnet_genesis, vec![], None)
}
