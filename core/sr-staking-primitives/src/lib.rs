
// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

#![cfg_attr(not(feature = "std"), no_std)]

//! A crate which contains primitives that are useful for implementation that uses staking
//! approaches in general. Definitions related to sessions, slashing, etc go here.

pub mod offence;

/// Simple index type with which we can count sessions.
pub type SessionIndex = u32;

/// A trait for fetching a validator id by the given index.
pub trait ValidatorIdByIndex<ValidatorId> {
	/// Return a validator identification by the given index in the current elected set of the era,
	// or `None` if `validator_index` is out of range.
	fn validator_id_by_index(validator_index: u32) -> Option<ValidatorId>;
}
