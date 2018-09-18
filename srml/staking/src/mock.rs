// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Test utilities

#![cfg(test)]

use primitives::BuildStorage;
use primitives::traits::{Identity};
use primitives::testing::{Digest, DigestItem, Header};
use substrate_primitives::{H256, Blake2Hasher, RlpCodec};
use runtime_io;
use {GenesisConfig, Module, Trait, consensus, session, system, timestamp, balances};

impl_outer_origin!{
	pub enum Origin for Test {}
}

// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
#[derive(Clone, PartialEq, Eq, Debug, Serialize, Deserialize)]
pub struct Test;
impl consensus::Trait for Test {
	const NOTE_OFFLINE_POSITION: u32 = 1;
	type Log = DigestItem;
	type SessionKey = u64;
	type OnOfflineValidator = ();
}
impl system::Trait for Test {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = ::primitives::traits::BlakeTwo256;
	type Digest = Digest;
	type AccountId = u64;
	type Header = Header;
	type Event = ();
	type Log = DigestItem;
}
impl balances::Trait for Test {
	type Balance = u64;
	type AccountIndex = u64;
	type OnFreeBalanceZero = Staking;
	type EnsureAccountLiquid = Staking;
	type Event = ();
}
impl session::Trait for Test {
	type ConvertAccountIdToSessionKey = Identity;
	type OnSessionChange = Staking;
	type Event = ();
}
impl timestamp::Trait for Test {
	const TIMESTAMP_SET_POSITION: u32 = 0;
	type Moment = u64;
}
impl Trait for Test {
	type OnRewardMinted = ();
	type Event = ();
}

pub fn new_test_ext(
	ext_deposit: u64,
	session_length: u64,
	sessions_per_era: u64,
	current_era: u64,
	monied: bool,
	reward: u64
) -> runtime_io::TestExternalities<Blake2Hasher, RlpCodec> {
	let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap();
	let balance_factor = if ext_deposit > 0 {
		256
	} else {
		1
	};
	t.extend(consensus::GenesisConfig::<Test>{
		code: vec![],
		authorities: vec![],
	}.build_storage().unwrap());
	t.extend(session::GenesisConfig::<Test>{
		session_length,
		validators: vec![10, 20],
	}.build_storage().unwrap());
	t.extend(balances::GenesisConfig::<Test>{
		balances: if monied {
			if reward > 0 {
				vec![(1, 10 * balance_factor), (2, 20 * balance_factor), (3, 30 * balance_factor), (4, 40 * balance_factor), (10, balance_factor), (20, balance_factor)]
			} else {
				vec![(1, 10 * balance_factor), (2, 20 * balance_factor), (3, 30 * balance_factor), (4, 40 * balance_factor)]
			}
		} else {
			vec![(10, balance_factor), (20, balance_factor)]
		},
		transaction_base_fee: 0,
		transaction_byte_fee: 0,
		existential_deposit: ext_deposit,
		transfer_fee: 0,
		creation_fee: 0,
		reclaim_rebate: 0,
	}.build_storage().unwrap());
	t.extend(GenesisConfig::<Test>{
		sessions_per_era,
		current_era,
		intentions: vec![10, 20],
		validator_count: 2,
		minimum_validator_count: 0,
		bonding_duration: sessions_per_era * session_length * 3,
		session_reward: reward,
		offline_slash: if monied { 20 } else { 0 },
		offline_slash_grace: 0,
	}.build_storage().unwrap());
	t.extend(timestamp::GenesisConfig::<Test>{
		period: 5
	}.build_storage().unwrap());
	runtime_io::TestExternalities::new(t)
}

pub type System = system::Module<Test>;
pub type Balances = balances::Module<Test>;
pub type Session = session::Module<Test>;
pub type Timestamp = timestamp::Module<Test>;
pub type Staking = Module<Test>;
