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

use std::collections::HashMap;
use rstd::prelude::*;
use codec::Encode;
use runtime_support::{StorageValue, StorageMap};
use primitives::traits::{Zero, As};
use substrate_primitives::KeccakHasher;
use {runtime_io, primitives};
use super::{Trait, Intentions, CurrentEra, OfflineSlashGrace, MinimumValidatorCount,
	BondingDuration, SessionsPerEra, ValidatorCount, SessionReward, EarlyEraSlash};

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct GenesisConfig<T: Trait> {
	pub sessions_per_era: T::BlockNumber,
	pub current_era: T::BlockNumber,
	pub intentions: Vec<T::AccountId>,
	pub validator_count: u32,
	pub minimum_validator_count: u32,
	pub bonding_duration: T::BlockNumber,
	pub session_reward: T::Balance,
	pub early_era_slash: T::Balance,
	pub offline_slash_grace: u32,
}

impl<T: Trait> GenesisConfig<T> where T::AccountId: From<u64> {
	pub fn simple() -> Self {
		GenesisConfig {
			sessions_per_era: T::BlockNumber::sa(2),
			current_era: T::BlockNumber::sa(0),
			intentions: vec![T::AccountId::from(1), T::AccountId::from(2), T::AccountId::from(3)],
			validator_count: 3,
			minimum_validator_count: 1,
			bonding_duration: T::BlockNumber::sa(0),
			session_reward: T::Balance::sa(0),
			early_era_slash: T::Balance::sa(0),
			offline_slash_grace: 1,
		}
	}

	pub fn extended() -> Self {
		GenesisConfig {
			sessions_per_era: T::BlockNumber::sa(3),
			current_era: T::BlockNumber::sa(1),
			intentions: vec![T::AccountId::from(1), T::AccountId::from(2), T::AccountId::from(3)],
			validator_count: 3,
			minimum_validator_count: 1,
			bonding_duration: T::BlockNumber::sa(0),
			session_reward: T::Balance::sa(0),
			early_era_slash: T::Balance::sa(0),
			offline_slash_grace: 1,
		}
	}
}

impl<T: Trait> Default for GenesisConfig<T> {
	fn default() -> Self {
		GenesisConfig {
			sessions_per_era: T::BlockNumber::sa(1000),
			current_era: T::BlockNumber::sa(0),
			intentions: vec![],
			validator_count: 0,
			minimum_validator_count: 0,
			bonding_duration: T::BlockNumber::sa(1000),
			session_reward: T::Balance::sa(0),
			early_era_slash: T::Balance::sa(0),
			offline_slash_grace: 0,
		}
	}
}

impl<T: Trait> primitives::BuildStorage for GenesisConfig<T> {
	fn build_storage(self) -> ::std::result::Result<HashMap<Vec<u8>, Vec<u8>>, String> {
		let mut r: runtime_io::TestExternalities<KeccakHasher> = map![
			Self::hash(<Intentions<T>>::key()).to_vec() => self.intentions.encode(),
			Self::hash(<SessionsPerEra<T>>::key()).to_vec() => self.sessions_per_era.encode(),
			Self::hash(<ValidatorCount<T>>::key()).to_vec() => self.validator_count.encode(),
			Self::hash(<MinimumValidatorCount<T>>::key()).to_vec() => self.minimum_validator_count.encode(),
			Self::hash(<BondingDuration<T>>::key()).to_vec() => self.bonding_duration.encode(),
			Self::hash(<CurrentEra<T>>::key()).to_vec() => self.current_era.encode(),
			Self::hash(<SessionReward<T>>::key()).to_vec() => self.session_reward.encode(),
			Self::hash(<EarlyEraSlash<T>>::key()).to_vec() => self.early_era_slash.encode(),
			Self::hash(<OfflineSlashGrace<T>>::key()).to_vec() => self.offline_slash_grace.encode()
		];
		Ok(r.into())
	}
}
