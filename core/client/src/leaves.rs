use std::collections::BTreeSet;
use std::cmp::{Ord, Ordering};
use kvdb::{KeyValueDB, DBTransaction};
use runtime_primitives::traits::SimpleArithmetic;
use codec::Decode;
use error;

// TODO [snd] put prefix here

/// helper wrapper type to keep a list of block hashes ordered
/// by `number` descending in a `BTreeSet` which allows faster and simpler
/// insertion and removal than keeping them in a list.
#[derive(Clone)]
struct LeafSetItem<H, N> {
	hash: H,
	number: N,
}

impl<H, N> Ord for LeafSetItem<H, N> where N: Ord {
	fn cmp(&self, other: &Self) -> Ordering {
		// reverse (descending) order
		other.number.cmp(&self.number)
	}
}

impl<H, N> PartialOrd for LeafSetItem<H, N> where N: PartialOrd {
	fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
		// reverse (descending) order
		other.number.partial_cmp(&self.number)
	}
}

impl<H, N> PartialEq for LeafSetItem<H, N> where N: PartialEq {
	fn eq(&self, other: &LeafSetItem<H, N>) -> bool {
		self.number == other.number
	}
}

impl<H, N> Eq for LeafSetItem<H, N> where N: PartialEq {}

/// list of leaf hashes ordered
/// stored in memory for fast access.
/// this allows very fast
#[derive(Clone)]
pub struct LeafSet<H, N> {
	storage: BTreeSet<LeafSetItem<H, N>>,
}

impl<H, N> LeafSet<H, N> where
	H: Clone + Decode,
	N: Clone + SimpleArithmetic + Decode,
{
	pub fn new() -> Self {
		Self {
			storage: BTreeSet::new()
		}
	}

	pub fn read_from_db(db: &KeyValueDB, column: Option<u32>, prefix: &[u8]) -> error::Result<Self> {
		let mut storage = BTreeSet::new();

		for (key, value) in db.iter_from_prefix(column, prefix) {
			let raw_hash = &mut &key[prefix.len()..];
			let hash = match Decode::decode(raw_hash) {
				Some(hash) => hash,
				None => return Err(error::ErrorKind::Backend("Error decoding hash".into()).into()),
			};
			let number = match Decode::decode(&mut &value[..]) {
				Some(number) => number,
				None => return Err(error::ErrorKind::Backend("Error decoding number".into()).into()),
			};
			storage.insert(LeafSetItem { hash, number });
		}
		Ok(Self { storage })
	}

	/// updating the leave list on import
	pub fn import(&mut self, hash: H, number: N, parent_hash: H) {
		// genesis block has no parent to remove
		if number != N::zero() {
			// remove parent
			self.storage.remove(&LeafSetItem {
				hash: parent_hash,
				number: number.clone() - N::one(),
			});
		}

		self.storage.insert(LeafSetItem { hash, number });
	}

	/// currently since revert only affects the canonical chain
	/// we assume that parent has no further children
	/// and we add it as leaf again
	pub fn revert(&mut self, hash: H, number: N, parent_hash: H) {
		self.storage.insert(LeafSetItem {
			hash: parent_hash,
			number: number.clone() - N::one(),
		});
		self.storage.remove(&LeafSetItem { hash, number });
	}

	/// returns an iterator over all hashes in the leaf set
	/// ordered by their block number descending.
	pub fn hashes(&self) -> Vec<H> {
		self.storage.iter().map(|item| item.hash.clone()).collect()
	}

	// /// modifies `transaction` to update
	// pub fn update_transaction(transaction: &mut DBTransaction, column: Option<u32>, prefix: &[u8], hash: H, number: N, parent_hash: H) {
	//	   transaction.put(column.clone(), 
	//	   transaction.delete(column, 
	// }
}

// TODO add tests
