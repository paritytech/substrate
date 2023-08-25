// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Sassafras inherents structures and helpers.

use sp_inherents::{Error, InherentData, InherentIdentifier};
use std::ops::Deref;

/// Inherent identifier.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"sassslot";

/// The type of inherent.
pub type InherentType = sp_consensus_slots::Slot;

/// Auxiliary trait to extract inherent data.
pub trait SassafrasInherentData {
	/// Get inherent data.
	fn sassafras_get_inherent_data(&self) -> Result<Option<InherentType>, Error>;
	/// Put inherent data.
	fn sassafras_put_inherent_data(&mut self, data: &InherentType) -> Result<(), Error>;
	/// Replace inherent data.
	fn sassafras_replace_inherent_data(&mut self, data: &InherentType);
}

impl SassafrasInherentData for InherentData {
	fn sassafras_get_inherent_data(&self) -> Result<Option<InherentType>, Error> {
		self.get_data(&INHERENT_IDENTIFIER)
	}

	fn sassafras_put_inherent_data(&mut self, data: &InherentType) -> Result<(), Error> {
		self.put_data(INHERENT_IDENTIFIER, data)
	}

	fn sassafras_replace_inherent_data(&mut self, data: &InherentType) {
		self.replace_data(INHERENT_IDENTIFIER, data);
	}
}

/// Provides the slot duration inherent data.
pub struct InherentDataProvider(InherentType);

impl InherentDataProvider {
	/// Create new inherent data provider from the given `slot`.
	pub fn new(slot: InherentType) -> Self {
		Self(slot)
	}

	/// Creates the inherent data provider by calculating the slot from the given
	/// `timestamp` and `duration`.
	pub fn from_timestamp(
		timestamp: sp_timestamp::Timestamp,
		slot_duration: sp_consensus_slots::SlotDuration,
	) -> Self {
		Self(InherentType::from_timestamp(timestamp, slot_duration))
	}
}

impl Deref for InherentDataProvider {
	type Target = InherentType;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

#[async_trait::async_trait]
impl sp_inherents::InherentDataProvider for InherentDataProvider {
	async fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), Error> {
		inherent_data.sassafras_put_inherent_data(&self.0)
	}
}
