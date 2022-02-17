// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/// Contains the inherents for the AURA module
use sp_inherents::{Error, InherentData, InherentIdentifier};

/// The Aura inherent identifier.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"auraslot";

/// The type of the Aura inherent.
pub type InherentType = sp_consensus_slots::Slot;

/// Auxiliary trait to extract Aura inherent data.
pub trait AuraInherentData {
	/// Get aura inherent data.
	fn aura_inherent_data(&self) -> Result<Option<InherentType>, Error>;
	/// Replace aura inherent data.
	fn aura_replace_inherent_data(&mut self, new: InherentType);
}

impl AuraInherentData for InherentData {
	fn aura_inherent_data(&self) -> Result<Option<InherentType>, Error> {
		self.get_data(&INHERENT_IDENTIFIER)
	}

	fn aura_replace_inherent_data(&mut self, new: InherentType) {
		self.replace_data(INHERENT_IDENTIFIER, &new);
	}
}

/// Provides the slot duration inherent data for `Aura`.
// TODO: Remove in the future. https://github.com/paritytech/substrate/issues/8029
#[cfg(feature = "std")]
pub struct InherentDataProvider {
	slot: InherentType,
}

#[cfg(feature = "std")]
impl InherentDataProvider {
	/// Create a new instance with the given slot.
	pub fn new(slot: InherentType) -> Self {
		Self { slot }
	}

	/// Creates the inherent data provider by calculating the slot from the given
	/// `timestamp` and `duration`.
	pub fn from_timestamp_and_duration(
		timestamp: sp_timestamp::Timestamp,
		duration: std::time::Duration,
	) -> Self {
		let slot =
			InherentType::from((timestamp.as_duration().as_millis() / duration.as_millis()) as u64);

		Self { slot }
	}
}

#[cfg(feature = "std")]
impl sp_std::ops::Deref for InherentDataProvider {
	type Target = InherentType;

	fn deref(&self) -> &Self::Target {
		&self.slot
	}
}

#[cfg(feature = "std")]
#[async_trait::async_trait]
impl sp_inherents::InherentDataProvider for InherentDataProvider {
	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), Error> {
		inherent_data.put_data(INHERENT_IDENTIFIER, &self.slot)
	}

	async fn try_handle_error(
		&self,
		_: &InherentIdentifier,
		_: &[u8],
	) -> Option<Result<(), Error>> {
		// There is no error anymore
		None
	}
}
