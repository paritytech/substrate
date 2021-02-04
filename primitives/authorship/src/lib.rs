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
use sp_runtime::{RuntimeString, traits::Block as BlockT};

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
pub trait UnclesInherentData<B: BlockT> {
	/// Get uncles.
	fn uncles(&self) -> Result<Vec<B::Header>, Error>;
}

impl<B: BlockT> UnclesInherentData<B> for InherentData {
	fn uncles(&self) -> Result<Vec<B::Header>, Error> {
		Ok(self.get_data(&INHERENT_IDENTIFIER)?.unwrap_or_default())
	}
}

/// Provider for inherent data.
#[cfg(feature = "std")]
pub struct InherentDataProvider<B: BlockT> {
	uncles: Vec<B::Header>
}

#[cfg(feature = "std")]
impl<B: BlockT> InherentDataProvider<B> {
	/// Create a new inherent data provider with the given `uncles`.
	pub fn new(uncles: Vec<B::Header>) -> Self {
		InherentDataProvider { uncles }
	}
}

#[cfg(feature = "std")]
impl<B: BlockT> sp_inherents::InherentDataProvider for InherentDataProvider<B> {
	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), Error> {
		inherent_data.put_data(INHERENT_IDENTIFIER, &self.uncles)
	}

	fn try_handle_error(
		&self,
		identifier: &InherentIdentifier,
		error: &[u8],
	) -> sp_inherents::TryHandleErrorResult {
		if *identifier != INHERENT_IDENTIFIER {
			return None
		}

		let error = InherentError::decode(&mut &error[..]).ok()?;

		Some(Box::pin(async move { Err(Box::from(format!("{:?}", error))) }))
	}
}
