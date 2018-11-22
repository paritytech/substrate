// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

// tag::description[]
//! Support code for the runtime.
// end::description[]

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]

#[cfg(feature = "std")]
extern crate serde;

#[macro_use]
extern crate srml_support_procedural;
#[doc(hidden)]
pub extern crate sr_std as rstd;
extern crate sr_io as runtime_io;
#[doc(hidden)]
pub extern crate sr_primitives as runtime_primitives;
extern crate substrate_metadata;

extern crate mashup;

#[macro_use]
extern crate pretty_assertions;
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate parity_codec_derive;

#[doc(hidden)]
pub extern crate parity_codec as codec;

/*
mod ex1 { 
decl_storage2! {
	trait Store for Module<T: Trait> as UpgradeKey {
		Key get(key) config(): T::AccountId;
	}
}
}
*/
mod ex2 { 
decl_storage2! {
	trait Store for Module<T: Trait> as CouncilMotions {
		/// The (hashes of) the active proposals.
		pub Proposals get(proposals): Vec<T::Hash>;
		/// Actual proposal for a given hash, if it's current.
		pub ProposalOf get(proposal_of): map T::Hash => Option< <T as Trait>::Proposal >;
		/// Votes for a given proposal: (required_yes_votes, yes_voters, no_voters).
		pub Voting get(voting): map T::Hash => Option<(ProposalIndex, u32, Vec<T::AccountId>, Vec<T::AccountId>)>;
		/// Proposals so far.
		pub ProposalCount get(proposal_count): u32;
	}
	add_extra_genesis {
		#[test] config(_marker): ::std::marker::PhantomData<T>;
		config(_marker2): ::std::marker::PhantomData<T>;
		build(|_, _| {});
	}
}
}
