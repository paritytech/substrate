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
use std::time::{Duration, Instant};

const COLLATION_LIFETIME: Duration = Duration::from_secs(60 * 5);

/// The role of the collator. Whether they're the primary or backup for this parachain.
#[derive(PartialEq, Debug, Clone, Copy, Encode, Decode)]
pub enum Role {
	/// Primary collators should send collations whenever it's time.
	Primary = 0,
	/// Backup collators should not.
	Backup = 1,
}

/// A maintenance action for the collator set.
#[derive(PartialEq, Debug)]
#[allow(dead_code)]
pub enum Action {
	/// Disconnect the given collator.
	Disconnect(AccountId),
	/// Give the collator a new role.
	NewRole(AccountId, Role),
}

struct CollationSlot {
	live_at: Instant,
	entries: SlotEntries,
}

impl CollationSlot {
	fn blank_now() -> Self {
		CollationSlot {
			live_at: Instant::now(),
			entries: SlotEntries::Blank,
		}
	}

	fn stay_alive(&self, now: Instant) -> bool {
		self.live_at + COLLATION_LIFETIME > now
	}
}

enum SlotEntries {
	Blank,
	// not queried yet
	Pending(Vec<Collation>),
	// waiting for next to arrive.
	Awaiting(Vec<oneshot::Sender<Collation>>),
}

impl SlotEntries {
	fn received_collation(&mut self, collation: Collation) {
		*self = match ::std::mem::replace(self, SlotEntries::Blank) {
			SlotEntries::Blank => SlotEntries::Pending(vec![collation]),
			SlotEntries::Pending(mut cs) => {
				cs.push(collation);
				SlotEntries::Pending(cs)
			}
			SlotEntries::Awaiting(senders) => {
				for sender in senders {
					let _ = sender.send(collation.clone());
				}

				SlotEntries::Blank
			}
		};
	}

	fn await_with(&mut self, sender: oneshot::Sender<Collation>) {
		*self = match ::std::mem::replace(self, SlotEntries::Blank) {
			SlotEntries::Blank => SlotEntries::Awaiting(vec![sender]),
			SlotEntries::Awaiting(mut senders) => {
				senders.push(sender);
				SlotEntries::Awaiting(senders)
			}
			SlotEntries::Pending(mut cs) => {
				let next_collation = cs.pop().expect("empty variant is always `Blank`; qed");
				let _ = sender.send(next_collation);

				if cs.is_empty() {
					SlotEntries::Blank
				} else {
					SlotEntries::Pending(cs)
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
	parachain_collators: HashMap<ParaId, ParachainCollators>,
	collations: HashMap<(Hash, ParaId), CollationSlot>,
}

impl CollatorPool {
	/// Create a new `CollatorPool` object.
	pub fn new() -> Self {
		CollatorPool {
			collators: HashMap::new(),
			parachain_collators: HashMap::new(),
			collations: HashMap::new(),
		}
	}

	/// Call when a new collator is authenticated. Returns the role.
	pub fn on_new_collator(&mut self, account_id: AccountId, para_id: ParaId) -> Role {
		self.collators.insert(account_id.clone(), para_id);
		match self.parachain_collators.entry(para_id) {
			Entry::Vacant(vacant) => {
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
	pub fn on_disconnect(&mut self, account_id: AccountId) -> Option<AccountId> {
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
						Some(collators.primary)
					}
				} else {
					let pos = occ.get().backup.iter().position(|a| a == &account_id)
						.expect("registered collator always present in backup if not primary; qed");

					occ.get_mut().backup.remove(pos);
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

			// TODO: punish if not primary?

			self.collations.entry((relay_parent, para_id.clone()))
				.or_insert_with(CollationSlot::blank_now)
				.entries
				.received_collation(collation);
		}
	}

	/// Wait for a collation from a parachain.
	pub fn await_collation(&mut self, relay_parent: Hash, para_id: ParaId, sender: oneshot::Sender<Collation>) {
		self.collations.entry((relay_parent, para_id))
			.or_insert_with(CollationSlot::blank_now)
			.entries
			.await_with(sender);
	}

	/// Call periodically to perform collator set maintenance.
	/// Returns a set of actions to perform on the network level.
	pub fn maintain_peers(&mut self) -> Vec<Action> {
		// TODO: rearrange periodically to new primary, evaluate based on latency etc.
		Vec::new()
	}

	/// called when a block with given hash has been imported.
	pub fn collect_garbage(&mut self, chain_head: Option<&Hash>) {
		let now = Instant::now();
		self.collations.retain(|&(ref h, _), slot| chain_head != Some(h) && slot.stay_alive(now));
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use polkadot_primitives::parachain::{CandidateReceipt, BlockData, HeadData};
	use substrate_primitives::H512;
	use futures::Future;

	#[test]
	fn disconnect_primary_gives_new_primary() {
		let mut pool = CollatorPool::new();
		let para_id: ParaId = 5.into();
		let bad_primary = [0; 32].into();
		let good_backup = [1; 32].into();

		assert_eq!(pool.on_new_collator(bad_primary, para_id.clone()), Role::Primary);
		assert_eq!(pool.on_new_collator(good_backup, para_id.clone()), Role::Backup);
		assert_eq!(pool.on_disconnect(bad_primary), Some(good_backup));
		assert_eq!(pool.on_disconnect(good_backup), None);
	}

	#[test]
	fn disconnect_backup_removes_from_pool() {
		let mut pool = CollatorPool::new();
		let para_id: ParaId = 5.into();
		let primary = [0; 32].into();
		let backup = [1; 32].into();

		assert_eq!(pool.on_new_collator(primary, para_id.clone()), Role::Primary);
		assert_eq!(pool.on_new_collator(backup, para_id.clone()), Role::Backup);
		assert_eq!(pool.on_disconnect(backup), None);
		assert!(pool.parachain_collators.get(&para_id).unwrap().backup.is_empty());
	}

	#[test]
	fn await_before_collation() {
		let mut pool = CollatorPool::new();
		let para_id: ParaId = 5.into();
		let primary = [0; 32].into();
		let relay_parent = [1; 32].into();

		assert_eq!(pool.on_new_collator(primary, para_id.clone()), Role::Primary);
		let (tx1, rx1) = oneshot::channel();
		let (tx2, rx2) = oneshot::channel();
		pool.await_collation(relay_parent, para_id, tx1);
		pool.await_collation(relay_parent, para_id, tx2);
		pool.on_collation(primary, relay_parent, Collation {
			receipt: CandidateReceipt {
				parachain_index: para_id,
				collator: primary.into(),
				signature: H512::from([2; 64]).into(),
				head_data: HeadData(vec![1, 2, 3]),
				balance_uploads: vec![],
				egress_queue_roots: vec![],
				fees: 0,
				block_data_hash: [3; 32].into(),
			},
			block_data: BlockData(vec![4, 5, 6]),
		});

		rx1.wait().unwrap();
		rx2.wait().unwrap();
	}

	#[test]
	fn collate_before_await() {
		let mut pool = CollatorPool::new();
		let para_id: ParaId = 5.into();
		let primary = [0; 32].into();
		let relay_parent = [1; 32].into();

		assert_eq!(pool.on_new_collator(primary, para_id.clone()), Role::Primary);

		pool.on_collation(primary, relay_parent, Collation {
			receipt: CandidateReceipt {
				parachain_index: para_id,
				collator: primary.into(),
				signature: H512::from([2; 64]).into(),
				head_data: HeadData(vec![1, 2, 3]),
				balance_uploads: vec![],
				egress_queue_roots: vec![],
				fees: 0,
				block_data_hash: [3; 32].into(),
			},
			block_data: BlockData(vec![4, 5, 6]),
		});

		let (tx, rx) = oneshot::channel();
		pool.await_collation(relay_parent, para_id, tx);
		rx.wait().unwrap();
	}

	#[test]
	fn slot_stay_alive() {
		let slot = CollationSlot::blank_now();
		let now = slot.live_at;

		assert!(slot.stay_alive(now));
		assert!(slot.stay_alive(now + Duration::from_secs(10)));
		assert!(!slot.stay_alive(now + COLLATION_LIFETIME));
		assert!(!slot.stay_alive(now + COLLATION_LIFETIME + Duration::from_secs(10)));
	}
}
