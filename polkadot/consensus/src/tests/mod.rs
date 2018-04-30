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

//! Common implementation of `polkadot-consensus` primitives
//! for a single file.

use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use ::collation::{Collators, Collation};
use ::SharedTable;

use parking_lot::Mutex;
use polkadot_primitives::Hash;
use polkadot_primitives::parachain::Id as ParaId;

use futures::prelude::*;
use futures::future;

#[derive(Clone)]
pub struct FakeCollators {
	inner: Arc<Mutex<HashMap<ParaId, Collation>>>
}

impl FakeCollators {
	fn new() -> Self {
		FakeCollators {
			inner: Arc::new(Mutex::new(HashMap::new()),)
		}
	}

	fn set_collation(&self, para_id: ParaId, collation: Collation) {
		self.inner.lock().insert()
	}
}

impl Collators for FakeCollators {
	type Error = (); // TODO: !
	type Collation = Box<Future<Item=Collation, Error=()>>;

	fn collate(&self, parachain: ParaId, relay_parent: Hash) -> Self::Collation {
		match self.inner.lock().get(para_id).cloned() {
			Some(collation) => Box::new(future::ok(collation)) as Box<_>,
			None => Box::new(future::empty()) as Box<_>,
		}
	}

	fn note_bad_collator(_collator: AccountId) {
		// TODO: testing when collations are bad.
	}
}

struct NetworkInner {

}

#[derive(Debug)]
pub struct Network {
	node_id: Arc<AtomicUsize>,
	inner: Arc<NetworkInner>,
}

impl ::consensus::Network for Network {

}

pub struct TableRouter(Network);
