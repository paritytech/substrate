// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

use sp_inherents::{InherentIdentifier, InherentData, Error};

/// The Aura inherent identifier.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"auraslot";

/// The type of the Aura inherent.
pub type InherentType = sp_consensus_slots::Slot;

/// Auxiliary trait to extract Aura inherent data.
pub trait AuraInherentData {
	/// Get aura inherent data.
	fn aura_inherent_data(&self) ->Result<InherentType, Error>;
}

impl AuraInherentData for InherentData {
	fn aura_inherent_data(&self) ->Result<InherentType, Error> {
		self.get_data(&INHERENT_IDENTIFIER)
			.and_then(|r| r.ok_or_else(|| "Aura inherent data not found".into()))
	}
}

/// Provides the slot duration inherent data for `Aura`.
#[cfg(feature = "std")]
pub struct InherentDataProvider {
	slot: InherentType,
}

#[cfg(feature = "std")]
impl InherentDataProvider {
	pub fn new(slot: InherentType) -> Self {
		Self {
			slot,
		}
	}
}

#[cfg(feature = "std")]
impl sp_inherents::InherentDataProvider for InherentDataProvider {
	fn provide_inherent_data(
		&self,
		inherent_data: &mut InherentData,
	) ->Result<(), Error> {
		inherent_data.put_data(INHERENT_IDENTIFIER, &self.slot)
	}

	fn try_handle_error(
		&self,
		identifier: &InherentIdentifier,
		error: &[u8],
	) -> sp_inherents::TryHandleErrorResult {
		use codec::Decode;

		if *identifier != INHERENT_IDENTIFIER {
			return None;
		}

		let error = sp_inherents::Error::decode(&mut &error[..]).ok()?;

		Some(Box::pin(async move { Err(Box::new(error) as Box<_>) }))
	}
}
