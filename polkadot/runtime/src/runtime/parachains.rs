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

//! Main parachains logic. For now this is just the determination of which validators do what.

use rstd::prelude::*;
use rstd::mem;
use codec::{Slicable, Joiner};
use support::{Hashable, with_env, storage};
use runtime::session;

const PARACHAIN_COUNT: &[u8] = b"par:cou";

/// Identifier for a chain, either one of a number of parachains or the relay chain.
#[derive(Copy, Clone, PartialEq)]
#[cfg_attr(test, derive(Debug))]
pub enum Chain {
	/// The relay chain.
	Relay,
	/// A parachain of the given index.
	Parachain(u32),
}

/// The duty roster specifying what jobs each validator must do.
#[derive(Clone, PartialEq)]
#[cfg_attr(test, derive(Default, Debug))]
pub struct DutyRoster {
	/// Lookup from validator index to chain on which that validator has a duty to validate.
	pub validator_duty: Vec<Chain>,
	/// Lookup from validator index to chain on which that validator has a duty to guarantee
	/// availability.
	pub guarantor_duty: Vec<Chain>,
}

/// Get the number of parachains registered at present.
pub fn parachain_count() -> u32 {
	storage::get_or(PARACHAIN_COUNT, 0)
}

/// Calculate the current block's duty roster.
pub fn calculate_duty_roster() -> DutyRoster {
	let parachain_count = parachain_count();
	let validator_count = session::validator_count() as u32;
	let validators_per_parachain = (validator_count - 1) / parachain_count;

	let mut roles_val = (0..validator_count).map(|i| match i {
		i if i < parachain_count * validators_per_parachain => Chain::Parachain(i / validators_per_parachain as u32),
		_ => Chain::Relay,
	}).collect::<Vec<_>>();
	let mut roles_gua = roles_val.clone();

	let h = with_env(|e| e.parent_hash.clone());
	let mut seed = Vec::<u8>::new().join(&h).join(b"validator_role_pairs").blake2_256();

	// shuffle
	for i in 0..(validator_count - 1) {
		// 8 bytes of entropy used per cycle, 32 bytes entropy per hash
		let offset = (i * 8 % 32) as usize;

		// number of roles remaining to select from.
		let remaining = (validator_count - i) as usize;

		// 4 * 2 32-bit ints per 256-bit seed.
		let val_index = u32::from_slice(&mut &seed[offset..offset + 4]).expect("using 4 bytes for a 32-bit quantity") as usize % remaining;
		let gua_index = u32::from_slice(&mut &seed[offset + 4..offset + 8]).expect("using 4 bytes for a 32-bit quantity") as usize % remaining;

		if offset == 24 {
			// into the last 8 bytes - rehash to gather new entropy
			seed = seed.blake2_256();
		}

		// exchange last item with randomly chosen first.
		roles_val.swap(remaining - 1, val_index);
		roles_gua.swap(remaining - 1, gua_index);
	}

	DutyRoster {
		validator_duty: roles_val,
		guarantor_duty: roles_gua,
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use codec::{KeyedVec, Joiner};
	use support::{one, two, with_env};
	use runtime::{consensus, session};

	fn simple_setup() -> TestExternalities {
		TestExternalities { storage: map![
			twox_128(b"ses:val:len").to_vec() => vec![].join(&8u32),
			twox_128(b"par:cou").to_vec() => vec![].join(&2u32)
		], }
	}

	#[test]
	fn should_work() {
		let mut t = simple_setup();
		with_externalities(&mut t, || {
			let check_roster = |duty_roster: &DutyRoster| {
				assert_eq!(duty_roster.validator_duty.len(), 8);
				assert_eq!(duty_roster.guarantor_duty.len(), 8);
				for i in 0..2 {
					assert_eq!(duty_roster.validator_duty.iter().filter(|&&j| j == Chain::Parachain(i)).count(), 3);
					assert_eq!(duty_roster.guarantor_duty.iter().filter(|&&j| j == Chain::Parachain(i)).count(), 3);
				}
				assert_eq!(duty_roster.validator_duty.iter().filter(|&&j| j == Chain::Relay).count(), 2);
				assert_eq!(duty_roster.guarantor_duty.iter().filter(|&&j| j == Chain::Relay).count(), 2);
			};

			with_env(|e| e.parent_hash = [0u8; 32].into());
			let duty_roster_0 = calculate_duty_roster();
			check_roster(&duty_roster_0);

			with_env(|e| e.parent_hash = [1u8; 32].into());
			let duty_roster_1 = calculate_duty_roster();
			check_roster(&duty_roster_1);
			assert!(duty_roster_0 != duty_roster_1);

			with_env(|e| e.parent_hash = [2u8; 32].into());
			let duty_roster_2 = calculate_duty_roster();
			check_roster(&duty_roster_2);
			assert!(duty_roster_0 != duty_roster_2);
			assert!(duty_roster_1 != duty_roster_2);
		});
	}
}
