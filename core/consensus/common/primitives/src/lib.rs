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

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Common consensus primitives.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Encode, Decode, Codec};
use client::decl_runtime_apis;
use rstd::vec::Vec;
use sr_primitives::traits::Header;

/// Represents an Babe equivocation proof.
#[cfg_attr(feature = "std", derive(Debug))]
#[derive(Clone, PartialEq, Eq, Decode, Encode)]
pub struct EquivocationProof<H, P, S> {
	pub reporter: P,
	pub identity: P,
	pub slot: u64,
	pub first_header: H,
	pub second_header: H,
	pub first_signature: S,
	pub second_signature: S,
}

decl_runtime_apis! {
	/// Common consensus runtime api.
	pub trait ConsensusApi<AuthorityId: Codec> {
		/// Returns the set of authorities of the currently active consensus mechanism.
		fn authorities() -> Vec<AuthorityId>;
	}
}