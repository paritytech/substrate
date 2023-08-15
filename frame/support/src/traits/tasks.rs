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

//! Contains the [`Task`] trait, which defines a general-purpose way for defining and executing
//! service work, and supporting types.

/// Contain's re-exports of all the supporting types for the [`Task`] trait. Used in the macro
/// expansion of `RuntimeTask`.
pub mod prelude {
	pub use codec::FullCodec;
	pub use scale_info::TypeInfo;
	pub use sp_runtime::DispatchError;
	pub use sp_std::{fmt::Debug, iter::Iterator};
	pub use sp_weights::Weight;
}

use prelude::*;

/// A general-purpose trait which defines a type of service work (i.e., work to performed by an
/// off-chain worker) including methods for enumerating, validating, indexing, and running
/// tasks of this type.
pub trait Task: Sized + FullCodec + TypeInfo + Clone + Debug + PartialEq + Eq {
	type Enumeration: Iterator<Item = Self>;

	/// A unique value representing this `Task`. Analogous to `call_index`, but for tasks.
	const TASK_INDEX: u64;

	/// Inspects the pallet's state and enumerates tasks of this type.
	fn enumerate() -> Self::Enumeration;

	/// Checks if a particular instance of this `Task` variant is a valid piece of work.
	fn is_valid(&self) -> bool;

	/// Performs the work for this particular `Task` variant.
	fn run(&self) -> Result<(), DispatchError>;

	/// Returns the weight of executing this `Task`.
	fn weight(&self) -> Weight;

	/// A unique value representing this `Task`. Analogous to `call_index`, but for tasks.
	fn task_index(&self) -> u64 {
		Self::TASK_INDEX
	}
}

/// Contains a subset of [`Task`] that can be generalized over the aggregated `RuntimeTask`
/// enum.
pub trait AggregatedTask: Sized + FullCodec + TypeInfo + Clone + Debug + PartialEq + Eq {
	/// Checks if a particular instance of this `Task` variant is a valid piece of work.
	fn is_valid(&self) -> bool;

	/// Performs the work for this particular `Task` variant.
	fn run(&self) -> Result<(), DispatchError>;

	/// Returns the weight of executing this `Task`.
	fn weight(&self) -> Weight;

	/// A unique value representing this `Task`. Analogous to `call_index`, but for tasks.
	fn task_index(&self) -> u64;
}
