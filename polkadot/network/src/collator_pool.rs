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

use futures::sync::oneshot;

use std::collections::hash_map::{HashMap, Entry};

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

enum CollationSlot {
	Blank,
	// not queried yet
	Pending(Vec<Collation>),
	// waiting for next to arrive.
	Awaiting(Vec<oneshot::Sender<Collation>>),
}

impl CollationSlot {
	fn received_collation(&mut self, collation: Collation) {
		*self = match ::std::mem::replace(self, CollationSlot::Blank) {
			CollationSlot::Blank => CollationSlot::Pending(vec![collation]),
			CollationSlot::Pending(mut cs) => {
				cs.push(collation);
				CollationSlot::Pending(cs)
			}
			CollationSlot::Awaiting(senders) => {
				for sender in senders {
					let _ = sender.send(collation.clone());
				}

				CollationSlot::Blank
			}
		};
	}

	fn await_with(&mut self, sender: oneshot::Sender<Collation>) {
		*self = match ::std::mem::replace(self, CollationSlot::Blank) {
			CollationSlot::Blank => CollationSlot::Awaiting(vec![sender]),
			CollationSlot::Awaiting(mut senders) => {
				senders.push(sender);
				CollationSlot::Awaiting(senders)
			}
			CollationSlot::Pending(mut cs) => {
				let next_collation = cs.pop().expect("empty variant is always `Blank`; qed");
				let _ = sender.send(next_collation);

				if cs.is_empty() {
					CollationSlot::Blank
				} else {
					CollationSlot::Pending(cs)
				}
			}
		};
	}
}

struct ParachainCollators {
	primary: AccountId,
	backup: Vec<AccountId>,
}

/// Manages connected collators and role assignments from the perspective of a validator.
pub struct CollatorPool {
	collators: HashMap<AccountId, ParaId>,
	bad_collators: Vec<AccountId>,
	parachain_collators: HashMap<ParaId, ParachainCollators>,
	collations: HashMap<(Hash, ParaId), CollationSlot>,
}

impl CollatorPool {
	/// Create a new `CollatorPool` object.
	pub fn new() -> Self {
		CollatorPool {
			collators: HashMap::new(),
			bad_collators: Vec::new(),
			parachain_collators: HashMap::new(),
			collations: HashMap::new(),
		}
	}

	/// Call when a new collator is authenticated. Returns the role.
	pub fn on_new_collator(&mut self, account_id: AccountId, para_id: ParaId) -> Role {
		self.collators.insert(account_id.clone(), para_id);
		match self.parachain_collators.entry(para_id) {
			Entry::Vacant(mut vacant) => {
				vacant.insert(ParachainCollators {
					primary: account_id,
					backup: Vec::new(),
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
	pub fn on_disconnect(&mut self, account_id: AccountId) -> Option<(AccountId, ParaId)> {
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

	/// Called when a collation is received.
	/// The collator should be registered for the parachain of the collation as a precondition of this function.
	/// The collation should have been checked for integrity of signature before passing to this function.
	pub fn on_collation(&mut self, account_id: AccountId, relay_parent: Hash, collation: Collation) {
		if let Some(para_id) = self.collators.get(&account_id) {
			debug_assert_eq!(para_id, &collation.receipt.parachain_index);

			self.collations.entry((relay_parent, para_id.clone()))
				.or_insert_with(|| CollationSlot::Blank)
				.received_collation(collation);
		}
	}

	/// Wait for a collation from a parachain.
	pub fn await_collation(&mut self, relay_parent: Hash, para_id: ParaId, sender: oneshot::Sender<Collation>) {
		self.collations.entry((relay_parent, para_id))
			.or_insert_with(|| CollationSlot::Blank)
			.await_with(sender);
	}

	/// Call periodically to perform collator set maintenance.
	/// Returns a set of actions to perform on the network level.
	pub fn maintain_peers(&mut self) -> Vec<Action> {
		// get rid of all bad peers.
		let mut actions = Vec::new();
		let bad = ::std::mem::replace(&mut self.bad_collators, Vec::new());
		for account in bad {
			actions.push(Action::Disconnect(account));
			if let Some((new_primary, _)) = self.on_disconnect(account) {
				actions.push(Action::NewRole(new_primary, Role::Primary));
			}
		}

		// TODO: put underperforming collators on the back-burner.

		actions
	}
}

#[cfg(test)]
mod tests {

}
