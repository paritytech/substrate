// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Build a balances genesis block.

#![cfg(feature = "std")]

use std::collections::HashMap;
use rstd::prelude::*;
use codec::Encode;
use runtime_support::{StorageValue, StorageMap};
use primitives::traits::{Zero, As};
use substrate_primitives::KeccakHasher;
use {runtime_io, primitives};
use super::{Trait, ENUM_SET_SIZE, EnumSet, NextEnumSet, CreationFee, TransferFee,
	ReclaimRebate, ExistentialDeposit, TransactionByteFee, TransactionBaseFee, TotalIssuance,
	FreeBalance};

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct GenesisConfig<T: Trait> {
	pub balances: Vec<(T::AccountId, T::Balance)>,
	pub transaction_base_fee: T::Balance,
	pub transaction_byte_fee: T::Balance,
	pub transfer_fee: T::Balance,
	pub creation_fee: T::Balance,
	pub reclaim_rebate: T::Balance,
	pub existential_deposit: T::Balance,
}

impl<T: Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		GenesisConfig {
			balances: vec![],
			transaction_base_fee: T::Balance::sa(0),
			transaction_byte_fee: T::Balance::sa(0),
			transfer_fee: T::Balance::sa(0),
			creation_fee: T::Balance::sa(0),
			existential_deposit: T::Balance::sa(0),
			reclaim_rebate: T::Balance::sa(0),
		}
	}
}

impl<T: Trait> primitives::BuildStorage for GenesisConfig<T> {
	fn build_storage(self) -> ::std::result::Result<HashMap<Vec<u8>, Vec<u8>>, String> {
		let total_issuance: T::Balance = self.balances.iter().fold(Zero::zero(), |acc, &(_, n)| acc + n);

		let mut r: runtime_io::TestExternalities<KeccakHasher> = map![
			Self::hash(<NextEnumSet<T>>::key()).to_vec() => T::AccountIndex::sa(self.balances.len() / ENUM_SET_SIZE).encode(),
			Self::hash(<TransactionBaseFee<T>>::key()).to_vec() => self.transaction_base_fee.encode(),
			Self::hash(<TransactionByteFee<T>>::key()).to_vec() => self.transaction_byte_fee.encode(),
			Self::hash(<TransferFee<T>>::key()).to_vec() => self.transfer_fee.encode(),
			Self::hash(<CreationFee<T>>::key()).to_vec() => self.creation_fee.encode(),
			Self::hash(<ExistentialDeposit<T>>::key()).to_vec() => self.existential_deposit.encode(),
			Self::hash(<ReclaimRebate<T>>::key()).to_vec() => self.reclaim_rebate.encode(),
			Self::hash(<TotalIssuance<T>>::key()).to_vec() => total_issuance.encode()
		];

		let ids: Vec<_> = self.balances.iter().map(|x| x.0.clone()).collect();
		for i in 0..(ids.len() + ENUM_SET_SIZE - 1) / ENUM_SET_SIZE {
			r.insert(Self::hash(&<EnumSet<T>>::key_for(T::AccountIndex::sa(i))).to_vec(),
				ids[i * ENUM_SET_SIZE..ids.len().min((i + 1) * ENUM_SET_SIZE)].to_owned().encode());
		}
		for (who, value) in self.balances.into_iter() {
			r.insert(Self::hash(&<FreeBalance<T>>::key_for(who)).to_vec(), value.encode());
		}
		Ok(r.into())
	}
}
