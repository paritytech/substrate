// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! FRAME module that tracks the last finalized block, as perceived by block authors.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_inherents::{InherentIdentifier, InherentData, Error};
use codec::Decode;

#[cfg(feature = "std")]
use codec::Encode;

/// The identifier for the `finalnum` inherent.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"finalnum";

/// Auxiliary trait to extract finalized inherent data.
pub trait FinalizedInherentData<N: Decode> {
	/// Get finalized inherent data.
	fn finalized_number(&self) -> Result<N, Error>;
}

impl<N: Decode> FinalizedInherentData<N> for InherentData {
	fn finalized_number(&self) -> Result<N, Error> {
		self.get_data(&INHERENT_IDENTIFIER)
			.and_then(|r| r.ok_or_else(|| "Finalized number inherent data not found".into()))
	}
}

/// Provider for inherent data.
#[cfg(feature = "std")]
pub struct InherentDataProvider<F, N> {
	inner: F,
	_marker: std::marker::PhantomData<N>,
}

#[cfg(feature = "std")]
impl<F, N> InherentDataProvider<F, N> {
	pub fn new(final_oracle: F) -> Self {
		InherentDataProvider { inner: final_oracle, _marker: Default::default() }
	}
}

#[cfg(feature = "std")]
impl<F, N: Encode> sp_inherents::ProvideInherentData for InherentDataProvider<F, N>
	where F: Fn() -> Result<N, Error>
{
	fn inherent_identifier(&self) -> &'static InherentIdentifier {
		&INHERENT_IDENTIFIER
	}

	fn provide_inherent_data(
		&self,
		inherent_data: &mut InherentData,
	) -> Result<(), Error> {
		(self.inner)()
			.and_then(|n| inherent_data.put_data(INHERENT_IDENTIFIER, &n))
	}

	fn error_to_string(&self, _error: &[u8]) -> Option<String> {
		Some(format!("no further information"))
	}
}
