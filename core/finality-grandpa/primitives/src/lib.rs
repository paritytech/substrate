// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Primitives for GRANDPA integration, suitable for WASM compilation.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate substrate_primitives;
extern crate sr_primitives;
extern crate parity_codec;

#[macro_use]
extern crate parity_codec_derive;

#[macro_use]
extern crate sr_api;

use substrate_primitives::AuthorityId;
use sr_primitives::traits::{Block as BlockT, DigestFor, NumberFor};

/// A scheduled change of authority set.
#[cfg_attr(feature = "std", derive(Debug, PartialEq))]
#[derive(Encode, Decode)]
pub struct ScheduledChange<N> {
	/// The new authorities after the change, along with their respective weights.
	pub next_authorities: Vec<(AuthorityId, u64)>,
	/// The number of blocks to delay.
	pub delay: N,
}

/// WASM function call to check for pending changes.
pub const PENDING_CHANGE_CALL: &str = "grandpa_pending_change";
/// WASM function call to get current GRANDPA authorities.
pub const AUTHORITIES_CALL: &str = "grandpa_pending_change";

decl_apis! {
	/// APIs for integrating the GRANDPA finality gadget into runtimes.
	///
	/// This is primarily used for negotiating authority-set changes for the
	/// gadget. GRANDPA uses a signalling model of changing authority sets:
	/// changes should be signalled with a delay of N blocks, and then automatically
	/// applied in the runtime after those N blocks have passed.
	///
	/// The consensus protocol will coordinate the handoff externally.
	pub trait Api<B: BlockT> {
		/// Check a digest for pending changes.
		/// Return `None` if there are no pending changes.
		///
		/// Precedence towards earlier or later digest items can be given
		/// based on the rules of the chain.
		///
		/// No change should be scheduled if one is already and the delay has not
		/// passed completely.
		fn grandpa_pending_change(digest: DigestFor<B>) -> Option<ScheduledChange<NumberFor<B>>>;

		/// Get the current GRANDPA authorities. This should not change except
		/// for when changes are scheduled and the corresponding delay has passed.
		fn grandpa_authorities() -> Vec<AuthorityId>;
	}
}
