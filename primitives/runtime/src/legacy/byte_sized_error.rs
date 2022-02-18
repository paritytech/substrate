// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Runtime types that existed prior to BlockBuilder API version 6.

use crate::{ArithmeticError, TokenError};
use codec::{Decode, Encode};
use scale_info::TypeInfo;
#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};

/// [`ModuleError`] type definition before BlockBuilder API version 6.
#[derive(Eq, Clone, Copy, Encode, Decode, Debug, TypeInfo)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct ModuleError {
	/// Module index, matching the metadata module index.
	pub index: u8,
	/// Module specific error value.
	pub error: u8,
	/// Optional error message.
	#[codec(skip)]
	#[cfg_attr(feature = "std", serde(skip_deserializing))]
	pub message: Option<&'static str>,
}

impl PartialEq for ModuleError {
	fn eq(&self, other: &Self) -> bool {
		(self.index == other.index) && (self.error == other.error)
	}
}

/// [`DispatchError`] type definition before BlockBuilder API version 6.
#[derive(Eq, Clone, Copy, Encode, Decode, Debug, TypeInfo, PartialEq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub enum DispatchError {
	/// Some error occurred.
	Other(
		#[codec(skip)]
		#[cfg_attr(feature = "std", serde(skip_deserializing))]
		&'static str,
	),
	/// Failed to lookup some data.
	CannotLookup,
	/// A bad origin.
	BadOrigin,
	/// A custom error in a module.
	Module(ModuleError),
	/// At least one consumer is remaining so the account cannot be destroyed.
	ConsumerRemaining,
	/// There are no providers so the account cannot be created.
	NoProviders,
	/// There are too many consumers so the account cannot be created.
	TooManyConsumers,
	/// An error to do with tokens.
	Token(TokenError),
	/// An arithmetic error.
	Arithmetic(ArithmeticError),
}

/// [`DispatchOutcome`] type definition before BlockBuilder API version 6.
pub type DispatchOutcome = Result<(), DispatchError>;

/// [`ApplyExtrinsicResult`] type definition before BlockBuilder API version 6.
pub type ApplyExtrinsicResult =
	Result<DispatchOutcome, crate::transaction_validity::TransactionValidityError>;

/// Convert the legacy `ApplyExtrinsicResult` type to the latest version.
pub fn convert_to_latest(old: ApplyExtrinsicResult) -> crate::ApplyExtrinsicResult {
	old.map(|outcome| {
		outcome.map_err(|e| match e {
			DispatchError::Other(s) => crate::DispatchError::Other(s),
			DispatchError::CannotLookup => crate::DispatchError::CannotLookup,
			DispatchError::BadOrigin => crate::DispatchError::BadOrigin,
			DispatchError::Module(err) => crate::DispatchError::Module(crate::ModuleError {
				index: err.index,
				error: [err.error, 0, 0, 0],
				message: err.message,
			}),
			DispatchError::ConsumerRemaining => crate::DispatchError::ConsumerRemaining,
			DispatchError::NoProviders => crate::DispatchError::NoProviders,
			DispatchError::TooManyConsumers => crate::DispatchError::TooManyConsumers,
			DispatchError::Token(err) => crate::DispatchError::Token(err),
			DispatchError::Arithmetic(err) => crate::DispatchError::Arithmetic(err),
		})
	})
}
