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

//! Authorship Primitives

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::{result::Result, prelude::*};

use codec::{Encode, Decode};
use sp_inherents::{Error, InherentIdentifier, InherentData, IsFatalError};
use sp_runtime::RuntimeString;

/// The identifier for the `uncles` inherent.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"uncles00";

/// Errors that can occur while checking the authorship inherent.
#[derive(Encode, sp_runtime::RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub enum InherentError {
	Uncles(RuntimeString),
}

impl IsFatalError for InherentError {
	fn is_fatal_error(&self) -> bool {
		match self {
			InherentError::Uncles(_) => true,
		}
	}
}

/// Auxiliary trait to extract uncles inherent data.
pub trait UnclesInherentData<H: Decode> {
	/// Get uncles.
	fn uncles(&self) -> Result<Vec<H>, Error>;
}

impl<H: Decode> UnclesInherentData<H> for InherentData {
	fn uncles(&self) -> Result<Vec<H>, Error> {
		Ok(self.get_data(&INHERENT_IDENTIFIER)?.unwrap_or_default())
	}
}

/// Provider for inherent data.
#[cfg(feature = "std")]
pub struct InherentDataProvider<F, H> {
	inner: F,
	_marker: std::marker::PhantomData<H>,
}

#[cfg(feature = "std")]
impl<F, H> InherentDataProvider<F, H> {
	pub fn new(uncles_oracle: F) -> Self {
		InherentDataProvider { inner: uncles_oracle, _marker: Default::default() }
	}
}

#[cfg(feature = "std")]
impl<F, H: Encode + std::fmt::Debug> sp_inherents::ProvideInherentData for InherentDataProvider<F, H>
where F: Fn() -> Vec<H>
{
	fn inherent_identifier(&self) -> &'static InherentIdentifier {
		&INHERENT_IDENTIFIER
	}

	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), Error> {
		let uncles = (self.inner)();
		if !uncles.is_empty() {
			inherent_data.put_data(INHERENT_IDENTIFIER, &uncles)
		} else {
			Ok(())
		}
	}

	fn error_to_string(&self, _error: &[u8]) -> Option<String> {
		Some(format!("no further information"))
	}
}
