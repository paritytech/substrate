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

use futures::{stream, Stream, Future, IntoFuture};
use primitives::parachain::{RawWitness, CollatedIngress, Header, Message, Id as ParaId};
use primitives::hash::H256;

/// A collation candidate.
pub struct Candidate {
	/// The header data.
	pub header: Header,
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
	type FutureEgress: IntoFuture<Item=Vec<Message>, Error=Self::Error>;

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
	-> Box<Future<Item=CollatedIngress, Error=R::Error> + 'a>
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
			let fetch = relay_context.remote_egress(para_id, ancestry_hash)
				.into_future()
				.map(move |q| (para_id, q));

			egress_fetch.push(fetch);

			if had_candidate && routed_at_hash.contains(&para_id) {
				to_remove.push(para_id);
			}
		}

		for para_id in to_remove {
			currently_routing.remove(&para_id);
		}

		if currently_routing.is_empty() { break }
	}

	let future = stream::futures_ordered(egress_fetch.into_iter().rev())
		.fold(Vec::new(), |mut v, x| { v.push(x); Ok(v) } )
		.map(CollatedIngress);

	Box::new(future)
}

#[cfg(test)]
mod tests {
	use super::*;

	use std::collections::{HashMap, BTreeSet};

	use futures::Future;
	use primitives::parachain::{Message, Id as ParaId};
	use primitives::hash::H256;

	pub struct DummyRelayChainCtx {
		blocks: Vec<(H256, bool)>,
		routing_parachains: HashMap<H256, BTreeSet<ParaId>>,
		egresses: HashMap<(ParaId, H256), Vec<Message>>,
		currently_routing: BTreeSet<ParaId>,
	}

	impl RelayChainContext for DummyRelayChainCtx {
		type Error = ();
		type FutureEgress = Result<Vec<Message>, ()>;
		type Ancestry = Box<Iterator<Item=(H256, bool)>>;

		fn routing_parachains(&self, block: Option<H256>) -> BTreeSet<ParaId> {
			match block {
				None => self.currently_routing.clone(),
				Some(block) => self.routing_parachains.get(&block).cloned().unwrap_or_default(),
			}
		}

		fn ancestry_iter(&self) -> Self::Ancestry {
			Box::new(self.blocks.clone().into_iter().rev())
		}

		fn remote_egress(&self, id: ParaId, block: H256) -> Result<Vec<Message>, ()> {
			Ok(self.egresses.get(&(id, block)).cloned().unwrap_or_default())
		}
	}

	fn fake_hash(x: u8) -> H256 {
		let mut hash = H256::default();
		hash[0] = x;
		hash
	}

    #[test]
	fn collates_ingress() {
		let route_from = |x: &[ParaId]| {
			 let mut set = BTreeSet::new();
			 set.extend(x.iter().cloned());
			 set
		};

		let message = |x: Vec<u8>| vec![Message(x)];

		let dummy_ctx = DummyRelayChainCtx {
			blocks: vec![
				(fake_hash(1), true),
				(fake_hash(2), false),
				(fake_hash(3), true),
				(fake_hash(4), false),
				(fake_hash(5), false),
			],
			routing_parachains: vec![
				(fake_hash(0), BTreeSet::new()),
				(fake_hash(1), route_from(&[2.into()])),
				(fake_hash(2), BTreeSet::new()),
				(fake_hash(3), route_from(&[3.into()])),
				(fake_hash(4), route_from(&[2.into()])),
				(fake_hash(5), BTreeSet::new()),
			].into_iter().collect(),
			currently_routing: route_from(&[2.into(), 3.into()]),
			egresses: vec![
				// these two will not be included because they are from before
				// the last successful times messages were routed from their
				// chains.
				((2.into(), fake_hash(0)), message(vec![200])),
				((3.into(), fake_hash(2)), message(vec![101, 102, 103])),

				// egresses for `2`: last routed successfully at 1.
				((2.into(), fake_hash(1)), message(vec![1, 2, 3])),
				((2.into(), fake_hash(2)), message(vec![4, 5, 6])),
				((2.into(), fake_hash(3)), message(vec![7, 8])),
				((2.into(), fake_hash(4)), message(vec![10])),
				((2.into(), fake_hash(5)), message(vec![12])),

				// egresses for `3`: last routed successfully at 3.
				((3.into(), fake_hash(3)), message(vec![9])),
				((3.into(), fake_hash(4)), message(vec![11])),
				((3.into(), fake_hash(5)), message(vec![13])),
			].into_iter().collect(),
		};

		assert_eq!(
			collate_ingress(dummy_ctx).wait().unwrap(),
			CollatedIngress(vec![
				(2.into(), message(vec![1, 2, 3])),
				(2.into(), message(vec![4, 5, 6])),
				(2.into(), message(vec![7, 8])),
				(3.into(), message(vec![9])),
				(2.into(), message(vec![10])),
				(3.into(), message(vec![11])),
				(2.into(), message(vec![12])),
				(3.into(), message(vec![13])),
			]
		))
	}
}
