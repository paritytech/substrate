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

//! Tool for creating the genesis block.

use std::collections::HashMap;
use runtime_std::twox_128;
use codec::{KeyedVec, Slicable};
use support::Hashable;
use primitives::{AccountID, BlockNumber, Block};
use runtime::staking::Balance;

/// Configuration of a general Polkadot genesis block.
pub struct GenesisConfig {
	pub validators: Vec<AccountID>,
	pub authorities: Vec<AccountID>,
	pub balances: Vec<(AccountID, Balance)>,
	pub block_time: u64,
	pub session_length: BlockNumber,
	pub sessions_per_era: BlockNumber,
	pub bonding_duration: u64,
	pub approval_ratio: u32,
}

impl GenesisConfig {
	pub fn new_simple(authorities_validators: Vec<AccountID>, balance: Balance) -> Self {
		GenesisConfig {
			validators: authorities_validators.clone(),
			authorities: authorities_validators.clone(),
			balances: authorities_validators.iter().map(|v| (v.clone(), balance)).collect(),
			block_time: 5,			// 5 second block time.
			session_length: 720,	// that's 1 hour per session.
			sessions_per_era: 24,	// 24 hours per era.
			bonding_duration: 90,	// 90 days per bond.
			approval_ratio: 667,	// 66.7% approvals required for legislation.
		}
	}

	pub fn genesis_map(&self) -> HashMap<Vec<u8>, Vec<u8>> {
		let wasm_runtime = include_bytes!("../../../../wasm-runtime/target/wasm32-unknown-unknown/release/runtime_polkadot.compact.wasm");
		vec![
			(&b":code"[..], wasm_runtime.to_vec()),
			(&b"gov:apr"[..], self.approval_ratio.to_vec()),
			(&b"ses:len"[..], self.session_length.to_vec()),
			(&b"ses:val:len"[..], (self.validators.len() as u32).to_vec()),
			(&b"con:aut:len"[..], (self.authorities.len() as u32).to_vec()),
			(&b"sta:wil:len"[..], 0u32.to_vec()),
			(&b"sta:spe"[..], self.sessions_per_era.to_vec()),
			(&b"sta:vac"[..], (self.validators.len() as u32).to_vec()),
			(&b"sta:era"[..], 0u64.to_vec()),
		].into_iter()
			.map(|(k, v)| (k.to_vec(), v))
			.chain(self.validators.iter()
				.enumerate()
				.map(|(i, account)| ((i as u32).to_keyed_vec(b"ses:val:"), account.to_vec()))
			).chain(self.authorities.iter()
				.enumerate()
				.map(|(i, account)| ((i as u32).to_keyed_vec(b"con:aut:"), account.to_vec()))
			).chain(self.balances.iter()
				.map(|&(account, balance)| (account.to_keyed_vec(b"sta:bal:"), balance.to_vec()))
			)
			.map(|(k, v)| (twox_128(&k[..])[..].to_vec(), v.to_vec()))
			.collect()
	}
}

pub fn additional_storage_with_genesis(genesis_block: &[u8]) -> Result<HashMap<Vec<u8>, Vec<u8>>, ()> {
	let h = Block::from_slice(genesis_block).ok_or(())?.header.blake2_256();
	Ok(map![
		twox_128(&0u64.to_keyed_vec(b"sys:old:")).to_vec() => h.to_vec()
	])
}
