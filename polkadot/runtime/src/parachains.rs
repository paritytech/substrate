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

use polkadot_primitives;
#[cfg(any(feature = "std", test))] use {runtime_io, runtime_primitives};
use rstd::prelude::*;
#[cfg(any(feature = "std", test))] use rstd::marker::PhantomData;
use codec::{Slicable, Joiner};
use runtime_support::Hashable;
#[cfg(any(feature = "std", test))] use runtime_support::StorageValue;
use runtime_primitives::traits::Executable;
use polkadot_primitives::parachain::{Id, Chain, DutyRoster};
use {system, session};

pub trait Trait: system::Trait<Hash = polkadot_primitives::Hash> + session::Trait {}

decl_module! {
	pub struct Module<T: Trait>;
}

decl_storage! {
	pub trait Store for Module<T: Trait>;
	// The number of parachains registered at present.
	pub Count get(count): b"para:count" => default u32;
}

impl<T: Trait> Module<T> {
	/// Calculate the current block's duty roster.
	pub fn calculate_duty_roster() -> DutyRoster {
		let parachain_count = Self::count();
		let validator_count = <session::Module<T>>::validator_count();
		let validators_per_parachain = (validator_count - 1) / parachain_count;

		let mut roles_val = (0..validator_count).map(|i| match i {
			i if i < parachain_count * validators_per_parachain =>
				Chain::Parachain(Id::from(i / validators_per_parachain as u32)),
			_ => Chain::Relay,
		}).collect::<Vec<_>>();
		let mut roles_gua = roles_val.clone();

		let h = <system::Module<T>>::random_seed();
		let mut seed = h.to_vec().and(b"validator_role_pairs").blake2_256();

		// shuffle
		for i in 0..(validator_count - 1) {
			// 8 bytes of entropy used per cycle, 32 bytes entropy per hash
			let offset = (i * 8 % 32) as usize;

			// number of roles remaining to select from.
			let remaining = (validator_count - i) as usize;

			// 4 * 2 32-bit ints per 256-bit seed.
			let val_index = u32::decode(&mut &seed[offset..offset + 4]).expect("using 4 bytes for a 32-bit quantity") as usize % remaining;
			let gua_index = u32::decode(&mut &seed[offset + 4..offset + 8]).expect("using 4 bytes for a 32-bit quantity") as usize % remaining;

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
}

impl<T: Trait> Executable for Module<T> {
	fn execute() {
	}
}

#[cfg(any(feature = "std", test))]
pub struct GenesisConfig<T: Trait> {
	pub count: u32,
	pub phantom: PhantomData<T>,
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		GenesisConfig {
			count: 0,
			phantom: PhantomData,
		}
	}
}

#[cfg(any(feature = "std", test))]
impl<T: Trait> runtime_primitives::BuildExternalities for GenesisConfig<T>
{
	fn build_externalities(self) -> runtime_io::TestExternalities {
		use runtime_io::twox_128;
		use codec::Slicable;
		map![
			twox_128(<Count<T>>::key()).to_vec() => self.count.encode()
		]
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::with_externalities;
	use substrate_primitives::H256;
	use runtime_primitives::BuildExternalities;
	use runtime_primitives::traits::{HasPublicAux, Identity};
	use runtime_primitives::testing::{Digest, Header};
	use consensus;

	pub struct Test;
	impl HasPublicAux for Test {
		type PublicAux = u64;
	}
	impl consensus::Trait for Test {
		type PublicAux = <Self as HasPublicAux>::PublicAux;
		type SessionKey = u64;
	}
	impl system::Trait for Test {
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = runtime_io::BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Header = Header;
	}
	impl session::Trait for Test {
		type ConvertAccountIdToSessionKey = Identity;
	}
	impl Trait for Test {}

	type System = system::Module<Test>;
	type Parachains = Module<Test>;

	fn new_test_ext() -> runtime_io::TestExternalities {
		let mut t = system::GenesisConfig::<Test>::default().build_externalities();
		t.extend(consensus::GenesisConfig::<Test>{
			code: vec![],
			authorities: vec![1, 2, 3],
		}.build_externalities());
		t.extend(session::GenesisConfig::<Test>{
			session_length: 1000,
			validators: vec![1, 2, 3, 4, 5, 6, 7, 8],
		}.build_externalities());
		t.extend(GenesisConfig::<Test>{
			count: 2,
			phantom: PhantomData,
		}.build_externalities());
		t
	}

	#[test]
	fn simple_setup_should_work() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Parachains::count(), 2);
		});
	}

	#[test]
	fn should_work() {
		with_externalities(&mut new_test_ext(), || {
			let check_roster = |duty_roster: &DutyRoster| {
				assert_eq!(duty_roster.validator_duty.len(), 8);
				assert_eq!(duty_roster.guarantor_duty.len(), 8);
				for i in (0..2).map(Id::from) {
					assert_eq!(duty_roster.validator_duty.iter().filter(|&&j| j == Chain::Parachain(i)).count(), 3);
					assert_eq!(duty_roster.guarantor_duty.iter().filter(|&&j| j == Chain::Parachain(i)).count(), 3);
				}
				assert_eq!(duty_roster.validator_duty.iter().filter(|&&j| j == Chain::Relay).count(), 2);
				assert_eq!(duty_roster.guarantor_duty.iter().filter(|&&j| j == Chain::Relay).count(), 2);
			};

			System::set_random_seed([0u8; 32].into());
			let duty_roster_0 = Parachains::calculate_duty_roster();
			check_roster(&duty_roster_0);

			System::set_random_seed([1u8; 32].into());
			let duty_roster_1 = Parachains::calculate_duty_roster();
			check_roster(&duty_roster_1);
			assert!(duty_roster_0 != duty_roster_1);

			System::set_random_seed([2u8; 32].into());
			let duty_roster_2 = Parachains::calculate_duty_roster();
			check_roster(&duty_roster_2);
			assert!(duty_roster_0 != duty_roster_2);
			assert!(duty_roster_1 != duty_roster_2);
		});
	}
}
