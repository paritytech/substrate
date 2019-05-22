// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Contract execution data.

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
#[cfg(feature = "std")]
use crate::bytes;
use rstd::vec::Vec;

/// Hierarchical Contract storage key.
/// Note that currently substrate is limited to two
/// level of storage.
/// Important property of this byte value are:
/// - ordering: smaller depth first
/// - hash: no conflict
/// - max 255 level (length in a single u8).
/// - key size limited to u32, BE format.
#[derive(PartialEq, Eq, Hash, PartialOrd, Ord, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct HStorageKey(#[cfg_attr(feature = "std", serde(with="bytes"))] Vec<u8>);

/// value for empty hierarchical storage key
pub const EMPTY_HSTORAGE_KEY: &'static [u8] = &[0];

impl HStorageKey {
	/// return empty HStorageKey
	pub fn empty() -> HStorageKey {
		HStorageKey(EMPTY_HSTORAGE_KEY.to_vec())
	}
	/// return the hirerachical key from its component
	/// only fail on number of level superior to 255
	pub fn new<I, K>(keys: I) -> Option<HStorageKey>
		where
			I: Iterator<Item=K>,
			K: AsRef<[u8]>,
	{
		match keys.size_hint() {
			(s, Some(e)) if s == e => {
				if s > 255 { return None };
				if s == 0 { return Some(Self::empty()) }
				let mut res = vec![0; 1 + ((s - 1) * 4)];
				res[0] = s as u8;
				let mut koff = 0;
				let mut keys = keys;
				if let Some(k) = keys.next() {
					res.extend_from_slice(k.as_ref());
					koff += k.as_ref().len();
				}
				let mut ix = 1;
				for k in keys {
					// should nether really happen
					if koff > u32::max_value() as usize { return None };
					res[ix..ix + 4].copy_from_slice(&(koff as u32).to_be_bytes());
					res.extend_from_slice(k.as_ref());
					ix += 4;
					koff += k.as_ref().len();
				}
				Some(HStorageKey(res))
			},
			_ => {
				let mut res = Self::empty();
				for k in keys {
					if !res.append(k.as_ref()) { return None };
				}
				Some(res)
			},
		}
	}

	/// add a child key. This method is slow, for building prefer new
	/// method.
	pub fn append(&mut self, key: &[u8]) -> bool {
		let next_len = self.len() + 1;
		if next_len > 255 { return false };
		let mut res = self.0.clone();
		if next_len != 1 {
			res.resize(res.len() + 4, 0);
			let head_ix = 1 + ((next_len - 1) * 4);
			let koff = res.len() - head_ix;
			let ix = 1 + ((next_len - 2) * 4);
			if koff > u32::max_value() as usize { return false };
			res[ix + 4..].copy_from_slice(&self.0[ix..]);
			res[ix..ix + 4].copy_from_slice(&(koff as u32).to_be_bytes());
		}
		res[0] = next_len as u8;
		res.extend_from_slice(key);
		self.0 = res;
		true
	}
	/// get the number of key
	pub fn len(&self) -> usize {
		self.0[0] as usize
	}

	/// get key slice at index
	/// start at 0
	pub fn get(&self, ix: usize) -> Option<&[u8]> {
		let mut le_buff = [0;4];
		let len =	self.len();
		if ix >= len {
			return None;
		}
		let head_ix = 1 + ((len - 1) * 4);
		let offset = if ix == 0 {
			head_ix
		} else {
			let s_ix = 1 + ((ix - 1) * 4);
			le_buff[..].copy_from_slice(&self.0[s_ix..s_ix + 4]);
			head_ix + u32::from_be_bytes(le_buff) as usize
		};
		let end_offset = if ix + 1 == len {
			self.0.len()
		} else {
			let s_ix = 1 + (ix * 4);
			le_buff[..].copy_from_slice(&self.0[s_ix..s_ix + 4]);
			head_ix + u32::from_be_bytes(le_buff) as usize
		};
		Some(&self.0[offset..end_offset])
	}

}

/// Contract storage key.
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, Hash, PartialOrd, Ord, Clone))]
pub struct StorageKey(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Contract storage entry data.
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, Hash, PartialOrd, Ord, Clone))]
pub struct StorageData(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Storage change set
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, PartialEq, Eq))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub struct StorageChangeSet<Hash> {
	/// Block hash
	pub block: Hash,
	/// A list of changes
	pub changes: Vec<(
		StorageKey,
		Option<StorageData>,
	)>,
}

/// List of all well known keys and prefixes in storage.
pub mod well_known_keys {

	/// Wasm code of the runtime.
	///
	/// Stored as a raw byte vector. Required by substrate.
	pub const CODE: &'static [u8] = b":code";

	/// Number of wasm linear memory pages required for execution of the runtime.
	///
	/// The type of this value is encoded `u64`.
	pub const HEAP_PAGES: &'static [u8] = b":heappages";

	/// Number of authorities.
	///
	/// The type of this value is encoded `u32`. Required by substrate.
	pub const AUTHORITY_COUNT: &'static [u8] = b":auth:len";

	/// Prefix under which authorities are storied.
	///
	/// The full key for N-th authority is generated as:
	///
	/// `(n as u32).to_keyed_vec(AUTHORITY_PREFIX)`.
	pub const AUTHORITY_PREFIX: &'static [u8] = b":auth:";

	/// Current extrinsic index (u32) is stored under this key.
	pub const EXTRINSIC_INDEX: &'static [u8] = b":extrinsic_index";

	/// Sum of all lengths of executed extrinsics (u32).
	pub const ALL_EXTRINSICS_LEN: &'static [u8] = b":all_extrinsics_len";

	/// Changes trie configuration is stored under this key.
	pub const CHANGES_TRIE_CONFIG: &'static [u8] = b":changes_trie";

	/// Prefix of child storage keys.
	pub const CHILD_STORAGE_KEY_PREFIX: &'static [u8] = b":child_storage:";

	/// Whether a key is a child storage key.
	///
	/// This is convenience function which basically checks if the given `key` starts
	/// with `CHILD_STORAGE_KEY_PREFIX` and doesn't do anything apart from that.
	pub fn is_child_storage_key(key: &[u8]) -> bool {
		// Other code might depend on this, so be careful changing this.
		key.starts_with(CHILD_STORAGE_KEY_PREFIX)
	}
}

#[cfg(test)]
mod test {
	use super::HStorageKey;

	#[test]
	fn basic_hstoragekey_test() {
		let data = [vec![1u8, 2], vec![3, 4, 5], vec![], vec![6]];
		let mut empty = HStorageKey::empty();
		assert_eq!(empty.len(), 0);
		assert_eq!(empty.get(0), None);
		assert_eq!(empty.get(1), None);
		empty.append(data[0].as_ref());
		assert_eq!(empty.len(), 1);
		assert_eq!(empty.get(0), Some(data[0].as_ref()));
		assert_eq!(empty.get(1), None);
		for i in 1..=3 {
			empty.append(data[i].as_ref());
			assert_eq!(empty.get(i), Some(data[i].as_ref()));
		}
		assert_eq!(empty.get(0), Some(data[0].as_ref()));
		let new = HStorageKey::new(data.iter()).unwrap();
		for i in 0..=3 {
			assert_eq!(new.get(i), Some(data[i].as_ref()));
		}
		assert_eq!(new.get(4), None);
		let mut empty = HStorageKey::empty();
		empty.append(&[]);
		assert_eq!(empty.get(0), Some(&[][..]));
		assert_eq!(empty.get(1), None);
	}

}
