// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Tool for creating the genesis block.

use codec::{KeyedVec, Joiner};
use std::collections::HashMap;
use runtime_io::twox_128;
use runtime_support::Hashable;
use primitives::Block;
use demo_primitives::{BlockNumber, AccountId};
use runtime::staking::Balance;
use runtime::{staking, session, consensus, system, democracy, council, council_vote};

/// Configuration of a general Substrate Demo genesis block.
pub struct GenesisConfig {
	pub validators: Vec<AccountId>,
	pub authorities: Vec<AccountId>,
	pub balances: Vec<(AccountId, Balance)>,
	pub block_time: u64,
	pub session_length: BlockNumber,
	pub sessions_per_era: BlockNumber,
	pub bonding_duration: BlockNumber,
	pub launch_period: BlockNumber,
	pub voting_period: BlockNumber,
	pub minimum_deposit: Balance,
	pub candidacy_bond: Balance,
	pub voter_bond: Balance,
	pub present_slash_per_voter: Balance,
	pub carry_count: u32,
	pub presentation_duration: BlockNumber,
	pub council_election_voting_period: BlockNumber,
	pub council_term_duration: BlockNumber,
	pub desired_seats: u32,
	pub inactive_grace_period: BlockNumber,
	pub cooloff_period: BlockNumber,
	pub council_proposal_voting_period: BlockNumber,
}

impl GenesisConfig {
	pub fn new_simple(authorities_validators: Vec<AccountId>, balance: Balance) -> Self {
		GenesisConfig {
			validators: authorities_validators.clone(),
			authorities: authorities_validators.clone(),
			balances: authorities_validators.iter().map(|v| (v.clone(), balance)).collect(),
			block_time: 30,			// 30 second block time.
			session_length: 120,	// that's 1 hour per session.
			sessions_per_era: 24,	// 24 hours per era.
			bonding_duration: 90,	// 90 days per bond.
			launch_period: 120 * 24 * 14,	// 2 weeks per public referendum
			voting_period: 120 * 24 * 28,	// 4 weeks to discuss & vote on an active referendum
			minimum_deposit: 1000,	// 1000 as the minimum deposit for a referendum
			candidacy_bond: 1000,	// 1000 to become a council candidate
			voter_bond: 100,		// 100 down to vote for a candidate
			present_slash_per_voter: 1,	// slash by 1 per voter for an invalid presentation.
			carry_count: 24,		// carry over the 24 runners-up to the next council election
			presentation_duration: 120 * 24,	// one day for presenting winners.
			council_election_voting_period: 7 * 120 * 24,	// one week period between possible council elections.
			council_term_duration: 180 * 120 * 24,	// 180 day term duration for the council.
			desired_seats: 0, // start with no council: we'll raise this once the stake has been dispersed a bit.
			inactive_grace_period: 1,	// one addition vote should go by before an inactive voter can be reaped.
			cooloff_period: 90 * 120 * 24, // 90 day cooling off period if council member vetoes a proposal.
			council_proposal_voting_period: 7 * 120 * 24, // 7 day voting period for council members.
		}
	}

	pub fn genesis_map(&self) -> HashMap<Vec<u8>, Vec<u8>> {
		let wasm_runtime = include_bytes!("../wasm/genesis.wasm").to_vec();
		vec![
			(&session::SESSION_LENGTH[..], vec![].and(&self.session_length)),
			(&session::VALIDATOR_COUNT[..], vec![].and(&(self.validators.len() as u32))),

			(&staking::INTENTION_COUNT[..], vec![].and(&0u32)),
			(&staking::SESSIONS_PER_ERA[..], vec![].and(&self.sessions_per_era)),
			(&staking::CURRENT_ERA[..], vec![].and(&0u64)),

			(&democracy::LAUNCH_PERIOD[..], vec![].and(&self.launch_period)),
			(&democracy::VOTING_PERIOD[..], vec![].and(&self.voting_period)),
			(&democracy::MINIMUM_DEPOSIT[..], vec![].and(&self.minimum_deposit)),

			(&council::CANDIDACY_BOND[..], vec![].and(&self.candidacy_bond)),
			(&council::VOTING_BOND[..], vec![].and(&self.voter_bond)),
			(&council::PRESENT_SLASH_PER_VOTER[..], vec![].and(&self.present_slash_per_voter)),
			(&council::CARRY_COUNT[..], vec![].and(&self.carry_count)),
			(&council::PRESENTATION_DURATION[..], vec![].and(&self.presentation_duration)),
			(&council::VOTING_PERIOD[..], vec![].and(&self.council_election_voting_period)),
			(&council::TERM_DURATION[..], vec![].and(&self.council_term_duration)),
			(&council::DESIRED_SEATS[..], vec![].and(&self.desired_seats)),
			(&council::INACTIVE_GRACE_PERIOD[..], vec![].and(&self.inactive_grace_period)),

			(&council_vote::COOLOFF_PERIOD[..], vec![].and(&self.cooloff_period)),
			(&council_vote::VOTING_PERIOD[..], vec![].and(&self.council_proposal_voting_period))
		].into_iter()
			.map(|(k, v)| (k.into(), v))
			.chain(self.validators.iter()
				.enumerate()
				.map(|(i, account)| ((i as u32).to_keyed_vec(session::VALIDATOR_AT), vec![].and(account)))
			).chain(self.balances.iter()
				.map(|&(account, balance)| (account.to_keyed_vec(staking::BALANCE_OF), vec![].and(&balance)))
			)
			.map(|(k, v)| (twox_128(&k[..])[..].to_vec(), v.to_vec()))
			.chain(vec![
				(system::CODE[..].into(), wasm_runtime),
				(consensus::AUTHORITY_COUNT[..].into(), vec![].and(&(self.authorities.len() as u32))),
			].into_iter())
			.chain(self.authorities.iter()
				.enumerate()
				.map(|(i, account)| ((i as u32).to_keyed_vec(consensus::AUTHORITY_AT), vec![].and(account)))
			)
			.collect()
	}
}

pub fn additional_storage_with_genesis(genesis_block: &Block) -> HashMap<Vec<u8>, Vec<u8>> {
	use codec::Slicable;
	map![
		twox_128(&0u64.to_keyed_vec(system::BLOCK_HASH_AT)).to_vec() => genesis_block.header.blake2_256().encode()
	]
}
