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



extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;

mod unfinalized;

use primitives::{Hash, blake2_256};
use codec::Slicable;
use std::collections::HashSet;
use unfinalized::UnfinalizedOverlay;

pub type DBValue = Vec<u8>;

pub trait KeyValueDb {
	type Error;

	fn get(&self, key: &Hash) -> Result<Option<DBValue>, Self::Error>;
}

#[cfg(test)]
impl KeyValueDb for ::std::collections::HashMap<Hash, DBValue> {
	type Error = ();
	fn get(&self, key: &Hash) -> Result<Option<DBValue>, ()> {
		Ok(::std::collections::HashMap::get(self, key).cloned())
	}
}

#[derive(Debug)]
pub enum Error<D: KeyValueDb> {
	Db(D::Error),
	Decoding,
}

#[derive(Default, Debug, Clone)]
pub struct Changeset {
	inserted: Vec<(Hash, DBValue)>,
	deleted: Vec<Hash>,
}

pub struct Constraints {
	max_blocks: Option<u32>,
	max_mem: Option<usize>,
}

pub enum Pruning {
	Constraints(Constraints),
	ArchiveAll,
	ArchiveCanonical,
}

struct CountedWindow;

impl CountedWindow {
	fn prune_one(&mut self, _deleted: &mut Vec<Hash>) {
	}

	fn note_finalized(&mut self, _hash: &Hash, _changeset: &Changeset) {
	}

	fn window_size(&self) -> u64 {
		0
	}

	fn next_hash(&self) -> Option<Hash> {
		None
	}

	fn mem_used(&self) -> usize {
		0
	}
}

fn to_key<S: Slicable>(prefix: &[u8], data: &S) -> Hash {
	let mut buffer = data.encode();
	buffer.extend(prefix);
	blake2_256(&buffer).into()
}

pub struct StateDb {
	mode: Pruning,
	unfinalized: UnfinalizedOverlay,
	pruning: Option<CountedWindow>,
	pinned: HashSet<Hash>,
}

impl StateDb {
	pub fn new<D: KeyValueDb>(mode: Pruning, db: &D) -> Result<StateDb, Error<D>> {
		let unfinalized = UnfinalizedOverlay::new(db)?;
		Ok(StateDb {
			mode,
			unfinalized,
			pruning: None,
			pinned: Default::default(),
		})
	}

	pub fn insert_block(&mut self, hash: &Hash, number: u64, parent_hash: &Hash, changeset: Changeset) -> Changeset {
		match self.mode {
			Pruning::ArchiveAll => {
				// write changes immediatelly
				changeset
			},
			Pruning::Constraints(_) | Pruning::ArchiveCanonical => {
				self.unfinalized.insert(hash, number, parent_hash, changeset)
			}
		}
	}

	pub fn finalize_block(&mut self, hash: &Hash) -> Changeset {
		let changeset = match self.mode {
			Pruning::ArchiveAll => {
				Changeset::default()
			},
			Pruning::Constraints(_) | Pruning::ArchiveCanonical => {
				self.unfinalized.finalize(hash)
			}
		};
		if let Some(ref mut pruning) = self.pruning {
			pruning.note_finalized(hash, &changeset);
		}
		changeset
	}

	pub fn prune(&mut self) -> Changeset {
		let mut deleted = Vec::new();
		if let (&mut Some(ref mut pruning), &Pruning::Constraints(ref constraints)) = (&mut self.pruning, &self.mode) {
			loop {
				if pruning.window_size() > constraints.max_blocks.unwrap_or(1) as u64 {
					break;
				}

				if constraints.max_mem.map_or(false, |m| pruning.mem_used() > m) {
					break;
				}

				let pinned = &self.pinned;
				if pruning.next_hash().map_or(false, |h| pinned.contains(&h)) {
					break;
				}

				pruning.prune_one(&mut deleted);
			}

			Changeset {
				inserted: Vec::new(),
				deleted,
			}
		}
		else {
			Changeset::default()
		}
	}

	pub fn pin(&mut self, hash: &Hash) {
		self.pinned.insert(*hash);
	}

	pub fn unpin(&mut self, hash: &Hash) {
		self.pinned.remove(hash);
	}

	pub fn get<D: KeyValueDb>(&self, key: &Hash, db: &D) -> Result<Option<DBValue>, Error<D>> {
		if let Some(value) = self.unfinalized.get(key) {
			return Ok(Some(value));
		}
		db.get(key).map_err(|e| Error::Db(e))
	}

	pub fn mem_used(&self) -> usize {
		0
	}
}

