// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use crate::{
	AuthorityId, BabeAuthorityWeight, BabeEpochConfiguration, BabeGenesisConfiguration, Epoch,
	NextEpochDescriptor, VRF_OUTPUT_LENGTH,
};
use codec::{Decode, Encode};
use sc_consensus_epochs::Epoch as EpochT;
use sp_consensus_slots::Slot;

/// BABE epoch information, version 0.
#[derive(Decode, Encode, PartialEq, Eq, Clone, Debug)]
pub struct EpochV0 {
	/// The epoch index.
	pub epoch_index: u64,
	/// The starting slot of the epoch.
	pub start_slot: Slot,
	/// The duration of this epoch.
	pub duration: u64,
	/// The authorities and their weights.
	pub authorities: Vec<(AuthorityId, BabeAuthorityWeight)>,
	/// Randomness for this epoch.
	pub randomness: [u8; VRF_OUTPUT_LENGTH],
}

impl EpochT for EpochV0 {
	type NextEpochDescriptor = NextEpochDescriptor;
	type Slot = Slot;

	fn increment(&self, descriptor: NextEpochDescriptor) -> EpochV0 {
		EpochV0 {
			epoch_index: self.epoch_index + 1,
			start_slot: self.start_slot + self.duration,
			duration: self.duration,
			authorities: descriptor.authorities,
			randomness: descriptor.randomness,
		}
	}

	fn start_slot(&self) -> Slot {
		self.start_slot
	}

	fn end_slot(&self) -> Slot {
		self.start_slot + self.duration
	}
}

impl EpochV0 {
	/// Migrate the sturct to current epoch version.
	pub fn migrate(self, config: &BabeGenesisConfiguration) -> Epoch {
		Epoch {
			epoch_index: self.epoch_index,
			start_slot: self.start_slot,
			duration: self.duration,
			authorities: self.authorities,
			randomness: self.randomness,
			config: BabeEpochConfiguration { c: config.c, allowed_slots: config.allowed_slots },
		}
	}
}
