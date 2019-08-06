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

use codec::Codec;
use client::decl_runtime_apis;
use rstd::vec::Vec;
use parity_codec::Codec;
#[cfg(feature = "std")]
use serde::Serialize;
use sr_primitives::{traits::{Header, Verify}};


decl_runtime_apis! {
	/// Common consensus runtime api.
	pub trait ConsensusApi<AuthorityId: Codec> {
		/// Returns the set of authorities of the currently active consensus mechanism.
		fn authorities() -> Vec<AuthorityId>;
	}
}

pub trait AuthorshipEquivocationProof {
	type Header: Header;
	type Signature: Verify;
	type Identity: Codec;

	/// Create an equivocation proof for AuRa or Babe.
	fn new(
		identity: Self::Identity,
		slot: u64,
		first_header: Self::Header,
		second_header: Self::Header,
		first_signature: Self::Signature, 
		second_signature: Self::Signature,
	) -> Self;

	/// Get the slot where the equivocation happened.
	fn slot(&self) -> u64;

	/// Get the identity of the suspect of equivocating.
	fn identity(&self) -> &Self::Identity;

	/// Get the first header involved in the equivocation.
	fn first_header(&self) -> &Self::Header;

	/// Get the second header involved in the equivocation.
	fn second_header(&self) -> &Self::Header;

	/// Get signature for the first header involved in the equivocation.
	fn first_signature(&self) -> &Self::Signature;

	/// Get signature for the second header involved in the equivocation.
	fn second_signature(&self) -> &Self::Signature;
}
