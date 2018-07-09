// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Bridge between the network and consensus service for getting collations to it.

use polkadot_primitives::{AccountId, Hash};
use polkadot_primitives::parachain::{Id as ParaId, Collation};
use substrate_network::{PeerId, Context};

use futures::prelude::*;
use futures::sync::oneshot;

use std::collections::hash_map::{HashMap, Entry};
use std::sync::Arc;
use parking_lot::Mutex;

/// The role of the collator. Whether they're the primary or backup for this parachain.
pub enum Role {
	/// Primary collators should send collations whenever it's time.
	Primary,
	/// Backup collators should not.
	Backup,
}

/// A maintenance action for the collator set.
pub enum Action {
	/// Disconnect the given collator.
	Disconnect(AccountId),
	/// Give the collator a new role.
	NewRole(AccountId, Role),
}

/// Manages connected collators and role assignments from the perspective of a validator.
#[derive(Clone)]
pub struct Collators {
	inner: Arc<Mutex<Inner>>,
}

impl Collators {
	/// Create a new `Collators` object.
	pub fn new() -> Self {
		Collators {
			inner: Arc::new(Mutex::new(Inner {
				collators: HashMap::new(),
				bad_collators: Vec::new(),
				parachain_collators: HashMap::new(),
			}))
		}
	}

	/// Call when a new collator is authenticated. Returns the role.
	pub fn on_new_collator(&self, account_id: AccountId, para_id: ParaId) -> Role {
		let mut inner = self.inner.lock();

		inner.collators.insert(account_id.clone(), para_id);
		match inner.parachain_collators.entry(para_id) {
			Entry::Vacant(mut vacant) => {
				vacant.insert(ParachainCollators {
					primary: account_id,
					backup: Vec::new(),
					collations: HashMap::new(),
				});

				Role::Primary
			},
			Entry::Occupied(mut occupied) => {
				occupied.get_mut().backup.push(account_id);

				Role::Backup
			}
		}
	}

	/// Called when a collator disconnects. If it was the primary, returns a new primary for that
	/// parachain.
	pub fn on_disconnect(&self, account_id: AccountId) -> Option<(AccountId, ParaId)> {
		self.inner.lock().on_disconnect(account_id)
	}

	/// Call periodically to perform collator set maintenance.
	/// Returns a set of actions.
	pub fn maintain_peers(&self) -> Vec<Action> {
		// get rid of all bad peers.
		let mut inner = self.inner.lock();
		let mut actions = Vec::new();
		let bad = ::std::mem::replace(&mut inner.bad_collators, Vec::new());
		for account in bad {
			actions.push(Action::Disconnect(account));
			if let Some((new_primary, _)) = inner.on_disconnect(account) {
				actions.push(Action::NewRole(new_primary, Role::Primary));
			}
		}

		// TODO: put underperforming collators on the back-burner.

		actions
	}
}

struct Inner {
	collators: HashMap<AccountId, ParaId>,
	bad_collators: Vec<AccountId>,
	parachain_collators: HashMap<ParaId, ParachainCollators>,
}

impl Inner {
	fn on_disconnect(&mut self, account_id: AccountId) -> Option<(AccountId, ParaId)> {
		self.collators.remove(&account_id).and_then(|para_id| match self.parachain_collators.entry(para_id) {
			Entry::Vacant(_) => None,
			Entry::Occupied(mut occ) => {
				if occ.get().primary == account_id {
					if occ.get().backup.is_empty() {
						occ.remove();
						None
					} else {
						let mut collators = occ.get_mut();
						collators.primary = collators.backup.pop().expect("backup non-empty; qed");
						Some((collators.primary, para_id))
					}
				} else {
					None
				}
			}
		})
	}
}

enum CollationSlot {
	// not queried yet
	Pending(Vec<Collation>),
	// waiting for next to arrive.
	Awaiting(oneshot::Sender<Collation>),
}

struct ParachainCollators {
	primary: AccountId,
	backup: Vec<AccountId>,
	collations: HashMap<Hash, CollationSlot>,
}

#[cfg(test)]
mod tests {

}
