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

//! Build a staking genesis block.

#![cfg(feature = "std")]

use rstd::prelude::*;
use runtime_io::twox_128;
use codec::Encode;
use runtime_support::{StorageValue, StorageMap};
use primitives::traits::{Zero, As};
use {runtime_io, primitives};
use super::{Trait, ENUM_SET_SIZE, EnumSet, NextEnumSet, Intentions, CurrentEra,
	BondingDuration, ContractFee, CreationFee, TransferFee, ReclaimRebate,
	ExistentialDeposit, TransactionByteFee, TransactionBaseFee, TotalStake,
	SessionsPerEra, ValidatorCount, FreeBalance, SessionReward, EarlyEraSlash};

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct GenesisConfig<T: Trait> {
	pub sessions_per_era: T::BlockNumber,
	pub current_era: T::BlockNumber,
	pub balances: Vec<(T::AccountId, T::Balance)>,
	pub intentions: Vec<T::AccountId>,
	pub validator_count: u64,
	pub bonding_duration: T::BlockNumber,
	pub transaction_base_fee: T::Balance,
	pub transaction_byte_fee: T::Balance,
	pub transfer_fee: T::Balance,
	pub creation_fee: T::Balance,
	pub contract_fee: T::Balance,
	pub reclaim_rebate: T::Balance,
	pub existential_deposit: T::Balance,
	pub session_reward: T::Balance,
	pub early_era_slash: T::Balance,
}

impl<T: Trait> GenesisConfig<T> where T::AccountId: From<u64> {
	pub fn simple() -> Self {
		GenesisConfig {
			sessions_per_era: T::BlockNumber::sa(2),
			current_era: T::BlockNumber::sa(0),
			balances: vec![(T::AccountId::from(1), T::Balance::sa(111))],
			intentions: vec![T::AccountId::from(1), T::AccountId::from(2), T::AccountId::from(3)],
			validator_count: 3,
			bonding_duration: T::BlockNumber::sa(0),
			transaction_base_fee: T::Balance::sa(0),
			transaction_byte_fee: T::Balance::sa(0),
			transfer_fee: T::Balance::sa(0),
			creation_fee: T::Balance::sa(0),
			contract_fee: T::Balance::sa(0),
			existential_deposit: T::Balance::sa(0),
			reclaim_rebate: T::Balance::sa(0),
			session_reward: T::Balance::sa(0),
			early_era_slash: T::Balance::sa(0),
		}
	}

	pub fn extended() -> Self {
		GenesisConfig {
			sessions_per_era: T::BlockNumber::sa(3),
			current_era: T::BlockNumber::sa(1),
			balances: vec![
				(T::AccountId::from(1), T::Balance::sa(10)),
				(T::AccountId::from(2), T::Balance::sa(20)),
				(T::AccountId::from(3), T::Balance::sa(30)),
				(T::AccountId::from(4), T::Balance::sa(40)),
				(T::AccountId::from(5), T::Balance::sa(50)),
				(T::AccountId::from(6), T::Balance::sa(60)),
				(T::AccountId::from(7), T::Balance::sa(1))
			],
			intentions: vec![T::AccountId::from(1), T::AccountId::from(2), T::AccountId::from(3)],
			validator_count: 3,
			bonding_duration: T::BlockNumber::sa(0),
			transaction_base_fee: T::Balance::sa(1),
			transaction_byte_fee: T::Balance::sa(0),
			transfer_fee: T::Balance::sa(0),
			creation_fee: T::Balance::sa(0),
			contract_fee: T::Balance::sa(0),
			existential_deposit: T::Balance::sa(0),
			reclaim_rebate: T::Balance::sa(0),
			session_reward: T::Balance::sa(0),
			early_era_slash: T::Balance::sa(0),
		}
	}
}

impl<T: Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		GenesisConfig {
			sessions_per_era: T::BlockNumber::sa(1000),
			current_era: T::BlockNumber::sa(0),
			balances: vec![],
			intentions: vec![],
			validator_count: 0,
			bonding_duration: T::BlockNumber::sa(1000),
			transaction_base_fee: T::Balance::sa(0),
			transaction_byte_fee: T::Balance::sa(0),
			transfer_fee: T::Balance::sa(0),
			creation_fee: T::Balance::sa(0),
			contract_fee: T::Balance::sa(0),
			existential_deposit: T::Balance::sa(0),
			reclaim_rebate: T::Balance::sa(0),
			session_reward: T::Balance::sa(0),
			early_era_slash: T::Balance::sa(0),
		}
	}
}

impl<T: Trait> primitives::BuildStorage for GenesisConfig<T> {
	fn build_storage(self) -> Result<runtime_io::TestExternalities, String> {
		let total_stake: T::Balance = self.balances.iter().fold(Zero::zero(), |acc, &(_, n)| acc + n);

		let mut r: runtime_io::TestExternalities = map![
			twox_128(<NextEnumSet<T>>::key()).to_vec() => T::AccountIndex::sa(self.balances.len() / ENUM_SET_SIZE).encode(),
			twox_128(<Intentions<T>>::key()).to_vec() => self.intentions.encode(),
			twox_128(<SessionsPerEra<T>>::key()).to_vec() => self.sessions_per_era.encode(),
			twox_128(<ValidatorCount<T>>::key()).to_vec() => self.validator_count.encode(),
			twox_128(<BondingDuration<T>>::key()).to_vec() => self.bonding_duration.encode(),
			twox_128(<TransactionBaseFee<T>>::key()).to_vec() => self.transaction_base_fee.encode(),
			twox_128(<TransactionByteFee<T>>::key()).to_vec() => self.transaction_byte_fee.encode(),
			twox_128(<TransferFee<T>>::key()).to_vec() => self.transfer_fee.encode(),
			twox_128(<CreationFee<T>>::key()).to_vec() => self.creation_fee.encode(),
			twox_128(<ContractFee<T>>::key()).to_vec() => self.contract_fee.encode(),
			twox_128(<ExistentialDeposit<T>>::key()).to_vec() => self.existential_deposit.encode(),
			twox_128(<ReclaimRebate<T>>::key()).to_vec() => self.reclaim_rebate.encode(),
			twox_128(<CurrentEra<T>>::key()).to_vec() => self.current_era.encode(),
			twox_128(<SessionReward<T>>::key()).to_vec() => self.session_reward.encode(),
			twox_128(<EarlyEraSlash<T>>::key()).to_vec() => self.early_era_slash.encode(),
			twox_128(<TotalStake<T>>::key()).to_vec() => total_stake.encode()
		];

		let ids: Vec<_> = self.balances.iter().map(|x| x.0.clone()).collect();
		for i in 0..(ids.len() + ENUM_SET_SIZE - 1) / ENUM_SET_SIZE {
			r.insert(twox_128(&<EnumSet<T>>::key_for(T::AccountIndex::sa(i))).to_vec(),
				ids[i * ENUM_SET_SIZE..ids.len().min((i + 1) * ENUM_SET_SIZE)].to_owned().encode());
		}
		for (who, value) in self.balances.into_iter() {
			r.insert(twox_128(&<FreeBalance<T>>::key_for(who)).to_vec(), value.encode());
		}
		Ok(r)
	}
}
