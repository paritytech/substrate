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

use sp_std::{prelude::*, result::Result};

#[cfg(feature = "std")]
use codec::Decode;
use codec::Encode;
use sp_inherents::{Error, InherentData, InherentIdentifier, IsFatalError};
use sp_runtime::{traits::Header as HeaderT, RuntimeString};

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
pub trait UnclesInherentData<H> {
	/// Get uncles.
	fn uncles(&self) -> Result<Vec<H>, Error>;
}

impl<H: HeaderT> UnclesInherentData<H> for InherentData {
	fn uncles(&self) -> Result<Vec<H>, Error> {
		Ok(self.get_data(&INHERENT_IDENTIFIER)?.unwrap_or_default())
	}
}

/// Provider for inherent data.
#[cfg(feature = "std")]
pub struct InherentDataProvider<H> {
	uncles: Vec<H>,
}

#[cfg(feature = "std")]
impl<H> InherentDataProvider<H> {
	/// Create a new inherent data provider with the given `uncles`.
	pub fn new(uncles: Vec<H>) -> Self {
		InherentDataProvider { uncles }
	}

	/// Create a new instance that is usable for checking inherents.
	///
	/// This will always return an empty vec of uncles.
	pub fn check_inherents() -> Self {
		Self { uncles: Vec::new() }
	}
}

#[cfg(feature = "std")]
#[async_trait::async_trait]
impl<H: HeaderT> sp_inherents::InherentDataProvider for InherentDataProvider<H> {
	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), Error> {
		inherent_data.put_data(INHERENT_IDENTIFIER, &self.uncles)
	}

	async fn try_handle_error(
		&self,
		identifier: &InherentIdentifier,
		error: &[u8],
	) -> Option<Result<(), Error>> {
		if *identifier != INHERENT_IDENTIFIER {
			return None
		}

		let error = InherentError::decode(&mut &error[..]).ok()?;

		Some(Err(Error::Application(Box::from(format!("{:?}", error)))))
	}
}
