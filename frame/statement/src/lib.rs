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

//! Supporting pallet for the statement store.
//!
//! - [`Pallet`]
//!
//! ## Overview
//!
//! The Statement pallet provides means to create and validate statements for the statement store.
//!

#![cfg_attr(not(feature = "std"), no_std)]

//use codec::{Decode, Encode, MaxEncodedLen};
use sp_statement_store::Statement;
use sp_statement_store::runtime_api::{StatementSource, ValidStatement, InvalidStatement};
use frame_support::sp_tracing::{enter_span, within_span, Level};

//mod mock;
//mod tests;

pub use pallet::*;

//const LOG_TARGET: &str = "runtime::statement";

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(sp_std::marker::PhantomData<T>);
}

impl<T: Config> Pallet<T> {
	pub fn validate_statement(
		_source: StatementSource,
		_statement: Statement,
	) -> Result<ValidStatement, InvalidStatement> {
		sp_io::init_tracing();

		enter_span! { Level::TRACE, "validate_statement" };


		within_span! {
			Level::TRACE, "validate";
		}
		Ok(ValidStatement {
			priority: 0,
			propagate: true,
		})
	}

}

