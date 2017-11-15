// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Collation Logic.
//!
//! A collator node lives on a distinct parachain and submits a proposal for
//! a state transition, along with a proof for its validity (what we call a witness).
//!
//! One of collators' other roles is to route messages between chains.
//! Each parachain produces a list of "egress" posts of messages for each other
//! parachain on each block, for a total of N^2 lists all together.
//!
//! We will refer to the egress list at relay chain block X of parachain A with
//! destination B as egress(X)[A -> B]
//!
//! On every block, each parachain will be intended to route messages from some
//! subset of all the other parachains.
//!
//! Since the egress information is unique to every block, when routing from a
//! parachain a collator must gather all egress posts from that parachain
//! up to the last point in history that messages were successfully routed
//! from that parachain, accounting for relay chain blocks where no candidate
//! from the collator's parachain was produced.
//!
//! In the case that all parachains route to each other and a candidate for the
//! collator's parachain was included in the last relay chain block, the collator
//! only has to gather egress posts from other parachains one block back in relay
//! chain history.
//!
//! This crate defines traits which provide context necessary for collation logic
//! to be performed, as the collation logic itself.

extern crate futures;
extern crate polkadot_primitives as primitives;

use std::collections::BTreeSet;

use futures::{stream, Stream, Future};
use primitives::parachain::{RawWitness, Message, Id as ParaId};
use primitives::hash::H256;

/// A collation candidate.
pub struct Candidate {
	/// The witness data.
	pub witness: RawWitness,
}

/// Parachain context needed for collation.
///
/// This can be implemented through an externally attached service or a stub.
pub trait ParachainContext {
	/// Produce a candidate, given the latest ingress queue information.
	fn produce_candidate<I: IntoIterator<Item=Message>>(
		&self,
		ingress: I,
	) -> Candidate;
}

/// Relay chain context needed to collate.
/// This encapsulates a network and local database which may store
/// some of the input.
pub trait RelayChainContext {
	type Error;
	type FutureEgress: Future<Item=Vec<Message>, Error=Self::Error>;

	/// Ancestry hashes of the relay chain, along with a flag indicating
	/// whether the local parachain had a candidate included.
	type Ancestry: IntoIterator<Item=(H256, bool)>;

	/// Provide a set of all parachains routed from at a block.
	///
	/// If `None`, provide the set meant to be routed from now.
	/// If the block hash is invalid, provide the empty set.
	fn routing_parachains(&self, block: Option<H256>) -> BTreeSet<ParaId>;

	/// Get an iterator over ancestry
	fn ancestry_iter(&self) -> Self::Ancestry;

	/// Get egress(block)[id -> local_id]
	fn remote_egress(&self, id: ParaId, block: H256) -> Self::FutureEgress;
}

/// Collate the necessary ingress queue using the given context.
pub fn collate_ingress<'a, R>(relay_context: R)
	-> Box<Future<Item=Vec<Message>, Error=R::Error> + 'a>
	where R: RelayChainContext,
		  R::Error: 'a,
		  R::FutureEgress: 'a
{
	let mut egress_fetch = Vec::new();
	let mut currently_routing = relay_context.routing_parachains(None);

	// follow the ancestry back up to the last point where
	// 1. the parachain was meant to be routed from
	// 2. there was a candidate included
	for (ancestry_hash, had_candidate) in relay_context.ancestry_iter() {
		let mut to_remove = Vec::new();
		let routed_at_hash = relay_context.routing_parachains(Some(ancestry_hash));

		// we reverse the order because we are also walking the ancestry backwards.
		// then we can collect all the futures in reverse order and get the
		// correctly ordered ingress queue.
		for para_id in currently_routing.iter().rev().cloned() {
			// fetch queue at the outset of `ancestry_hash` regardless.
			egress_fetch.push(relay_context.remote_egress(para_id, ancestry_hash));

			if had_candidate && routed_at_hash.contains(&para_id) {
				to_remove.push(para_id);
			}
		}

		for para_id in to_remove {
			currently_routing.remove(&para_id);
		}
	}

	let future = stream::futures_ordered(egress_fetch.into_iter().rev())
		.fold(Vec::new(), |mut v, e| { v.extend(e); Ok(v) } );

	Box::new(future)
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
    }
}
