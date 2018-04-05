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

//! Validator-side view of collation.
//!
//! This module contains type definitions, a trait for a batch of collators, and a trait for
//! attempting to fetch a collation repeatedly until a valid one is obtained.

use std::sync::Arc;

use polkadot_api::PolkadotApi;
use polkadot_primitives::{Hash, Timestamp};
use polkadot_primitives::parachain::{Id as ParaId, DutyRoster, BlockData, Extrinsic, CandidateReceipt};
use primitives::block::{Block as SubstrateBlock, Header as SubstrateHeader, HeaderHash, Id as BlockId, Number as BlockNumber};
use primitives::AuthorityId;

use futures::prelude::*;

/// A full collation.
pub struct Collation {
	/// Block data.
	pub block_data: BlockData,
	/// Extrinsic data.
	pub extrinsic: Extrinsic,
	/// The candidate receipt itself.
	pub receipt: CandidateReceipt,
}

/// Encapsulates connections to collators and allows collation on any parachain.
pub trait Collators {
	/// Errors when producing collations.
	type Error;
	/// A full collation.
	type Collation: IntoFuture<Item=Collation,Error=Self::Error>;

	/// Collate on a specific parachain, building on a given relay chain parent hash.
	fn collate(&self, parachain: ParaId, relay_parent: Hash) -> Self::Collation;

	/// Note a bad collator. TODO: take proof
	fn note_bad_collator(&self, collator: Address);
}

/// A future which resolves when a collation is available.
///
/// This future is fused.
pub struct CollationFetch<C: Collators, P: PolkadotApi> {
	parachain: ParaId,
	relay_parent: Hash,
	collators: Arc<C>,
	live_fetch: Option<C::Collation>,
	client: Arc<P>,
	done: bool,
}

impl<C: Collators, P: PolkadotApi> CollationFetch<C, P> {
	/// Create a new collation fetcher.
	pub fn new(parachain: ParaId, relay_parent: Hash, collators: Arc<C>, client: Arc<P>) -> Self {
		CollationFetch {
			parachain,
			relay_parent,
			collators,
			client,
			live_fetch: None,
			done: false,
		}
	}
}

impl<C: Collators, P: PolkadotApi> Future for CollationFetch<C, P> {
	type Item = Collation;
	type Error = C::Error;

	fn poll(&mut self) -> Poll<Collation, C::Error> {
		if self.done { return Ok(Async::NotReady) }
		loop {
			let x = {
				let (p, r, c)  = (&self.parachain, &self.relay_parent, &self.collators);
				try_ready!(self.live_fetch.get_or_insert_with(|| c.collate(p, r)).poll())
			};

			if verify_collation(&self.client, &self.relay_parent, &x) {
				self.done = true;
				return Ok(Async::Ready(x));
			} else {
				self.live_fetch = None;
				self.collators.note_bad_collator(x.receipt.collator);
			}
		}
	}
}

/// Check whether a given collation is valid.
pub fn verify_collation<P: PolkadotApi>(_client: P, _relay_parent: Hash, collation: &Collation) -> bool {
	true // TODO: actually check this.
}
