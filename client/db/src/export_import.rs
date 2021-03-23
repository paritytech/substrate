// This file is part of Substrate.

// Copyright (C) 2021-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Snapshot export and import implementation.

use log::info;
use sc_client_api::{SnapshotSync, SnapshotConfig,
	DatabaseError, StateVisitor};
use sp_blockchain::{
	Error as ClientError,
};
use codec::{Decode, Encode, Compact, IoReader};
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{
	Block as BlockT, Header as HeaderT, NumberFor, One
};
use crate::utils::meta_keys;
use sp_blockchain::HeaderBackend;
use crate::{utils, columns, Backend};
use sp_core::storage::{ChildType, ChildInfo, PrefixedStorageKey};
use std::collections::btree_map::BTreeMap;

/// Component of client needed to do snapshot import and export.
pub struct ClientSnapshotSync<Block: BlockT> {
	pub(crate) backend: Backend<Block>,
}

/// First byte of snapshot define
/// its mode.
#[repr(u8)]
enum SnapshotMode {
	/// Flat variant, no compression, and obviously no diff.
	Flat = 0,
}

struct HeaderRanges<N> {
	inner: Vec<(N, N)>,
}

impl<N: Ord> HeaderRanges<N> {
	fn new() -> Self {
		HeaderRanges {
			inner: Vec::new()
		}
	}

	fn insert(&mut self, item: (N, N)) {
		// unoptimized but we should not have to many components
		// declaration to merge.
		let mut i = 0;
		for range in self.inner.iter_mut() {
			if item.1 < range.0 {
				break;
			}
			if item.1 <= range.1 {
				if item.0 < range.0 {
					range.0 = item.0;
				}
				return;
			}
			if item.0 <= range.1 {
				range.1 = item.1;
				return;
			}
			i += 1;
		}
		self.inner.insert(i, item)
	}

	fn insert_all(&mut self, items: impl Iterator<Item = (N, N)>) {
		for item in items {
			self.insert(item);
		}
	}
}

impl<Block: BlockT> SnapshotSync<Block> for ClientSnapshotSync<Block> {
	fn export_sync(
		&self,
		mut out_dyn: &mut dyn std::io::Write,
		range: SnapshotConfig<Block>,
	) -> sp_blockchain::Result<()> {

		// dyn to impl
		let out = &mut out_dyn;

		// version
		out.write(&[0u8]).map_err(|e|
			sp_blockchain::Error::Backend(format!("Snapshot export error: {:?}", e)),
		)?;
		// info to init 'Meta' (need to allow read_meta and all pointing to to)
		//let to_hash = self.hash(to)?;
		range.to.encode_to(out);
		//to_hash.encode_to(out);
		// get range
		let nb = range.to - range.from;
		nb.encode_to(out);
		let mut header_ranges = HeaderRanges::<NumberFor<Block>>::new();
		header_ranges.insert((range.from, range.to));
		// registered components
		let registered_snapshot_sync = self.backend.blockchain.registered_snapshot_sync.read();
		let nb = registered_snapshot_sync.len();
		Compact(nb as u32).encode_to(out);
		for i in 0..nb {
			let mut ranges = registered_snapshot_sync[i].export_sync_meta(
				out_dyn,
				&range,
			)?;
			header_ranges.insert_all(ranges.additional_headers.drain(..));
		}

		// dyn to impl
		let out = &mut out_dyn;

		for range in header_ranges.inner.into_iter() {
			let mut i = range.0;
			while i <= range.1 {
				let header: Block::Header = self.backend.blockchain.header(BlockId::Number(i))?
					.ok_or_else(|| sp_blockchain::Error::Backend(
						format!("Header missing at {:?}", i),
					))?;
				header.encode_to(out);
				i += One::one();
			}
		}

		out_dyn.write(&[SnapshotMode::Flat as u8])
			.map_err(|e| DatabaseError(Box::new(e)))?;

		flat_from_backend(out_dyn, &self.backend, &range.to_hash)?;

		Ok(())
	}

	fn import_sync(
		&self,
		encoded: &mut dyn std::io::Read,
	) -> sp_blockchain::Result<SnapshotConfig<Block>> {
		let mut buf = [0];
		// version
		encoded.read_exact(&mut buf[..1]).map_err(|e|
			sp_blockchain::Error::Backend(format!("Snapshot import error: {:?}", e)),
		)?;
		match buf[0] {
			b if b == 0 => (),
			_ => return Err(sp_blockchain::Error::Backend("Invalid snapshot version.".into())),
		}
		let mut reader = IoReader(encoded);
		let to: NumberFor<Block> = Decode::decode(&mut reader).map_err(|e|
			sp_blockchain::Error::Backend(format!("Snapshot import error: {:?}", e)),
		)?;
		/*let to_hash: Block::Hash = Decode::decode(&mut reader).map_err(|e|
			sp_blockchain::Error::Backend(format!("Snapshot import error: {:?}", e)),
		)?;*/
		let nb: NumberFor<Block> = Decode::decode(&mut reader).map_err(|e|
			sp_blockchain::Error::Backend(format!("Snapshot import error: {:?}", e)),
		)?;
		let mut range = SnapshotConfig::<Block> {
			from: to - nb,
			from_hash: Default::default(),
			to,
			to_hash: Default::default(),
		};

		// registered components
		let registered_snapshot_sync = self.backend.blockchain.registered_snapshot_sync.read();
		let expected = registered_snapshot_sync.len();
		let nb: Compact<u32> = Decode::decode(&mut reader).map_err(|e|
			sp_blockchain::Error::Backend(format!("Snapshot import error: {:?}", e)),
		)?;

		if nb.0 as usize != expected {
			return Err(sp_blockchain::Error::Backend("Invalid registerd component count.".into()));
		}

		let mut header_ranges = HeaderRanges::<NumberFor<Block>>::new();
		header_ranges.insert((range.from.clone(), range.to.clone()));
		for i in 0..expected {
			let mut ranges = registered_snapshot_sync[i].import_sync_meta(
				reader.0,
				&range,
			)?;
			header_ranges.insert_all(ranges.additional_headers.drain(..));
		}

		for header_range in header_ranges.inner.into_iter() {

			let mut i = header_range.0;
			while i <= header_range.1 {
				let mut transaction = Default::default();
				let header: Block::Header = Decode::decode(&mut reader).map_err(|e|
					sp_blockchain::Error::Backend(format!("Snapshot import error: {:?}", e)),
				)?;
				let hash = header.hash();
				let parent_hash = header.parent_hash().clone();
				let number = header.number().clone();
				let lookup_key = utils::number_and_hash_to_lookup_key(number, hash)?;

				utils::insert_hash_to_key_mapping(
					&mut transaction,
					columns::KEY_LOOKUP,
					number,
					hash,
				)?;

				// canonical blocks got a number mapping
				utils::insert_number_to_key_mapping(
					&mut transaction,
					columns::KEY_LOOKUP,
					number,
					hash,
				)?;


				transaction.set_from_vec(columns::HEADER, &lookup_key, header.encode());

				if i == range.to {
					use sp_runtime::SaturatedConversion;
					range.to_hash = header.hash().clone();
					// init state_db persistence
					self.backend.storage.state_db.last_canonical_base(
						&header.parent_hash(),
						i.clone().saturated_into::<u64>() - 1,
					);
				}

				if i == range.from {
					// add parent of i as best and finalize (next steps would be to import this block.
					let number = i - One::one();
					range.from_hash = header.hash().clone();
					let hash = header.parent_hash().clone();
					let lookup_key = utils::number_and_hash_to_lookup_key(number, hash)?;
					utils::insert_hash_to_key_mapping(
						&mut transaction,
						columns::KEY_LOOKUP,
						number,
						hash,
					)?;

					self.backend.blockchain.update_meta(hash.clone(), number.clone(), true, true);
					transaction.set_from_vec(columns::META, meta_keys::BEST_BLOCK, lookup_key.clone());
					transaction.set_from_vec(columns::META, meta_keys::FINALIZED_BLOCK, lookup_key);
				}
				i += One::one();
				let mut leaves = self.backend.blockchain.leaves.write();
				let _displaced_leaf = leaves.import(hash, number, parent_hash);
				leaves.prepare_transaction(&mut transaction, columns::META, meta_keys::LEAF_PREFIX);

				self.backend.blockchain.db.commit(transaction)?;
			}
		}

		let mut buf = [0];
		reader.0.read_exact(&mut buf[..1])
			.map_err(|e| DatabaseError(Box::new(e)))?;
		match buf[0] {
			u if u == SnapshotMode::Flat as u8 => true,
			_ => {
				let e = ClientError::StateDatabase("Unknown snapshot mode.".into());
				return Err(e);
			},
		};

		debug_assert!(range.from_hash == range.to_hash);
		let state_hash = range.to_hash.clone();

		// Load all in memory.
		let mut top_state: Vec<(Vec<u8>, Vec<u8>)> = Default::default();
		let mut children_state: BTreeMap<Vec<u8>, Vec<(Vec<u8>, Vec<u8>)>> = Default::default();
		snapshot_state_visit(&mut reader.0, |child_key, key, value| {
			if let Some(child_key) = child_key {
				let prefixed_child_key = ChildInfo::new_default(child_key).prefixed_storage_key();
				children_state.entry(prefixed_child_key.into_inner())
					.or_default().push((key.to_vec(), value));
			} else {
				top_state.push((key.to_vec(), value));
			}
			Ok(())
		})?;

		// header is imported by 'import_sync_meta'.
		let header = self.backend.blockchain.header(BlockId::Hash(state_hash.clone()))?
			.expect("Missing header");
		let expected_root = header.state_root().clone();
		use sc_client_api::backend::{Backend, BlockImportOperation};
		let mut op = self.backend.begin_operation()?;
		self.backend.begin_state_operation(&mut op, BlockId::Hash(Default::default()))?;
		info!("Initializing import block/state (header-hash: {})",
			state_hash,
		);
		let data: sp_database::StateIter = (
			Box::new(top_state.into_iter()),
			Box::new(children_state.into_iter().map(|(key, state)| {
				let child_iter: sp_database::ChildStateIter = Box::new(state.into_iter());
				(key, child_iter)
			})),
		);
		let state_root = op.inject_finalized_state(data)
			.map_err(|e| DatabaseError(Box::new(e)))?;
		// TODO get state root from header and pass as param
		if expected_root != state_root {
			panic!("Unexpected root {:?}, in header {:?}.", state_root, expected_root);
		}
		// only state import, but need to have pending block to commit actual data.
		op.set_block_data(
			header,
			None,
			None,
			sc_client_api::NewBlockState::Final,
		).map_err(|e| DatabaseError(Box::new(e)))?;
		self.backend.commit_operation(op)
			.map_err(|e| DatabaseError(Box::new(e)))?;

		Ok(range)
	}
}

/// First byte of snapshot define
/// its mode.
#[repr(u8)]
enum StateId {
	/// End of state.
	/// This allow putting state payload in non final position.
	EndOfState = 0,
	/// Top state
	Top = 1,
	/// Default child trie, followed by unprefixed path from default trie prefix.
	/// Path is a KeyDelta from previous child trie.
	DefaultChild = 2,
}

enum KeyDelta {
	Augment(usize),
	PopAugment(usize, usize),
	// last is a pop augment with a 0 size pop
	// So 1
	Last,
}

impl Encode for KeyDelta {
	fn size_hint(&self) -> usize {
		2
	}

	fn encode_to<T: codec::Output + ?Sized>(&self, out: &mut T) {
		match self {
			KeyDelta::Augment(nb) => {
				let augment_nb = nb * 2; // 0 as last bit
				Compact(augment_nb as u64).encode_to(out);
			},
			KeyDelta::PopAugment(nb, nb2) => {
				let pop_nb = (nb * 2) + 1; // 1 as last bit
				Compact(pop_nb as u64).encode_to(out);
				Compact(*nb2 as u64).encode_to(out);
			},
			KeyDelta::Last => {
				let pop_nb = (0 * 2) + 1; // 1 as last bit
				Compact(pop_nb as u64).encode_to(out);
			},
		}
	}
}

impl Decode for KeyDelta {
	fn decode<I: codec::Input>(input: &mut I) -> Result<Self, codec::Error> {
		let first = Compact::<u64>::decode(input)?.0;
		if first % 2 == 0 {
			Ok(KeyDelta::Augment((first / 2) as usize))
		} else {
			let pop_size = first / 2;
			if pop_size == 0 {
				return Ok(KeyDelta::Last);
			}
			let second = Compact::<u64>::decode(input)?.0;
			Ok(KeyDelta::PopAugment(pop_size as usize, second as usize))
		}
	}
}



/// Key are written in delta mode (since they are sorted it is a big size gain).
struct KeyWriter {
	previous: Vec<u8>,
}

fn common_depth(v1: &[u8], v2: &[u8]) -> usize {
	let upper_bound = std::cmp::min(v1.len(), v2.len());
	for a in 0 .. upper_bound {
		if v1[a] != v2[a] {
			return a;
		}
	}
	upper_bound
}

impl KeyWriter {
	fn write_next(&mut self, next: Vec<u8>, out: &mut (impl codec::Output + ?Sized)) {
		let previous = &self.previous[..];
		let common = common_depth(previous, next.as_slice());
		let keydelta = if common < previous.len() {
			KeyDelta::PopAugment(previous.len() - common, next.len() - common)
		} else {
			KeyDelta::Augment(next.len() - common)
		};
		keydelta.encode_to(out);
		out.write(&next[common..]);
		self.previous = next;
	}

	fn write_last(&mut self, out: &mut (impl codec::Output + ?Sized)) {
		KeyDelta::Last.encode_to(out);
		self.previous = [][..].into();
	}
}

/// Key are read in delta mode (since they are sorted it is a big size gain).
struct KeyReader {
	previous: Vec<u8>,
}

impl KeyReader {
	fn read_next<I: codec::Input>(&mut self, input: &mut I)  -> Result<Option<&[u8]>, codec::Error> {
		let nb = match KeyDelta::decode(input)? {
			KeyDelta::Last => {
				self.previous.clear();
				return Ok(None);
			},
			KeyDelta::Augment(nb) => nb,
			KeyDelta::PopAugment(nb, nb2) => {
				let old_len = self.previous.len();
				if old_len < nb {
					return Err("Invalid keydiff encoding".into());
				}
				self.previous.truncate(old_len - nb);
				nb2
			},
		};
		let old_len = self.previous.len();
		self.previous.resize(old_len + nb, 0);
		input.read(&mut self.previous[old_len..])?;
		Ok(Some(self.previous.as_slice()))
	}
}

/// Create flat snapshot from backend.
pub(crate) fn flat_from_backend<Block: BlockT>(
	mut out: &mut dyn std::io::Write,
	backend: &impl sc_client_api::Backend<Block>,
	block_hash: &Block::Hash,
) -> sp_database::error::Result<()> {
	out.write(&[StateId::Top as u8])
		.map_err(|e| DatabaseError(Box::new(e)))?;

	let mut default_key_writer = KeyWriter {
		previous: [][..].into(),
	};
	let default_key_writer = &mut default_key_writer;
	let mut default_child_key_writer = KeyWriter {
		previous: Default::default(),
	};
	let default_child_key_writer = &mut default_child_key_writer;

	let mut last_child: Option<Vec<u8>> = None;
	let last_child = &mut last_child;
	let mut child_storage_key = PrefixedStorageKey::new(Vec::new());
	let child_storage_key = &mut child_storage_key;
	let state_visit = StateVisitor::<Block, _>(backend, block_hash);
	state_visit.state_visit(|child, key, value| {
		if child != last_child.as_ref().map(Vec::as_slice) {
			default_key_writer.write_last(&mut out);
			if let Some(child) = child.as_ref() {
				*child_storage_key = PrefixedStorageKey::new(child.to_vec());
				*last_child = Some(child.to_vec());
				match ChildType::from_prefixed_key(&child_storage_key) {
					Some((ChildType::ParentKeyId, storage_key)) => {
						out.write(&[StateId::DefaultChild as u8])
							.map_err(|e| DatabaseError(Box::new(e)))?;
						default_child_key_writer.write_next(storage_key.to_vec(), &mut out);
					},
					_ => {
						let e = ClientError::StateDatabase("Unknown child trie type in state".into());
						return Err(DatabaseError(Box::new(e)));
					},
				}
			} else {
				out.write(&[StateId::Top as u8])
					.map_err(|e| DatabaseError(Box::new(e)))?;
			}
			*default_key_writer = KeyWriter {
				previous: Default::default(),
			};
		}
		default_key_writer.write_next(key, &mut out);
		value.encode_to(&mut out);
		Ok(())
	})?;

	default_key_writer.write_last(&mut out);
	out.write(&[StateId::EndOfState as u8])
		.map_err(|e| DatabaseError(Box::new(e)))?;
	Ok(())
}

/// Visit state stored on snapshot.
pub(crate) fn snapshot_state_visit(
	mut from: &mut dyn std::io::Read,
	mut visitor: impl FnMut(Option<&[u8]>, &[u8], Vec<u8>) -> std::result::Result<(), DatabaseError>,
) -> std::result::Result<(), DatabaseError> {
	let mut key_reader = KeyReader {
		previous: Vec::new(),
	};
	let mut default_child_key_reader = KeyReader {
		previous: Vec::new(),
	};

	let mut buf = [0];
	loop {
		from.read_exact(&mut buf[..1])
			.map_err(|e| DatabaseError(Box::new(e)))?;
		match buf[0] {
			u if u == StateId::Top as u8 => {
				while let Some(key) = key_reader.read_next(&mut IoReader(&mut from))
						.map_err(|e| DatabaseError(Box::new(e)))? {
					let value: Vec<u8> = Decode::decode(&mut IoReader(&mut from))
						.map_err(|e| DatabaseError(Box::new(e)))?;
					visitor(None, key, value)?;
				}
			},
			u if u == StateId::DefaultChild as u8 => {
				let child_key = if let Some(child_key) = default_child_key_reader.read_next(&mut IoReader(&mut from))
					.map_err(|e| DatabaseError(Box::new(e)))? {
						child_key
				} else {
					let e = ClientError::StateDatabase("Unexpected child key encoding.".into());
					return Err(DatabaseError(Box::new(e)));
				};
				//let child_info = ChildInfo::new_default(child_key);
				while let Some(key) = key_reader.read_next(&mut IoReader(&mut from))
					.map_err(|e| DatabaseError(Box::new(e)))? {
					let value = Decode::decode(&mut IoReader(&mut from))
						.map_err(|e| DatabaseError(Box::new(e)))?;
					visitor(Some(child_key), key, value)?;
				}
			},
			u if u == StateId::EndOfState as u8 => {
				break;
			},
			_ => {
				let e = ClientError::StateDatabase("Unknown state type.".into());
				return Err(DatabaseError(Box::new(e)));
			},
		}
	}
	Ok(())
}

#[test]
fn key_writer_reader_encode_decode() {
	let keys = [
		vec![17u8, 243, 186, 46, 28, 221, 109, 98, 242, 255, 155, 85, 137, 231, 255,
			129, 186, 127, 184, 116, 87, 53, 220, 59, 226, 162, 198, 26, 114, 195,
			158, 120],
		vec![24, 9, 215, 131, 70, 114, 122, 14, 245, 140, 15, 160, 59, 175, 163, 35,
			135, 141, 67, 77, 97, 37, 180, 4, 67, 254, 17, 253, 41, 45, 19, 164],
		vec![26, 115, 109, 55, 80, 76, 46, 63, 183, 61, 173, 22, 12, 85, 178, 145,
			135, 141, 67, 77, 97, 37, 180, 4, 67, 254, 17, 253, 41, 45, 19, 164],
		vec![28, 182, 243, 110, 2, 122, 187, 32, 145, 207, 181, 17, 10, 181, 8, 127,
			6, 21, 91, 60, 217, 168, 201, 229, 233, 162, 63, 213, 220, 19, 165, 237],
		vec![28, 182, 243, 110, 2, 122, 187, 32, 145, 207, 181, 17, 10, 181, 8, 127,
			94, 6, 33, 196, 134, 154, 166, 12, 2, 190, 154, 220, 201, 138, 13, 29],
		vec![28, 182, 243, 110, 2, 122, 187, 32, 145, 207, 181, 17, 10, 181, 8, 127,
			102, 232, 240, 53, 200, 173, 190, 127, 21, 71, 180, 60, 81, 230, 248, 164],
		vec![28, 182, 243, 110, 2, 122, 187, 32, 145, 207, 181, 17, 10, 181, 8, 127,
			103, 135, 17, 209, 94, 187, 206, 186, 92, 208, 206, 161, 88, 230, 103, 90],
		vec![28, 182, 243, 110, 2, 122, 187, 32, 145, 207, 181, 17, 10, 181, 8, 127,
			135, 141, 67, 77, 97, 37, 180, 4, 67, 254, 17, 253, 41, 45, 19, 164],
		vec![28, 182, 243, 110, 2, 122, 187, 32, 145, 207, 181, 17, 10, 181, 8, 127,
			170, 207, 0, 185, 180, 31, 218, 122, 146, 104, 130, 28, 42, 43, 62, 76],
		vec![32, 153, 215, 241, 9, 214, 229, 53, 251, 0, 11, 186, 98, 63, 212, 64,
			76, 1, 78, 107, 248, 184, 194, 192, 17, 231, 41, 11, 133, 105, 107, 179],
		vec![32, 153, 215, 241, 9, 214, 229, 53, 251, 0, 11, 186, 98, 63, 212, 64,
			135, 141, 67, 77, 97, 37, 180, 4, 67, 254, 17, 253, 41, 45, 19, 164],
	];
	let mut dest = Vec::new();
	let mut writer = KeyWriter {
		previous: [][..].into(),
	};
	for key in keys.iter() {
		writer.write_next(key.clone(), &mut dest)
	}
	writer.write_last(&mut dest);
	let mut decoded = Vec::new();
	let mut key_reader = KeyReader {
		previous: Vec::new(),
	};
	let input = &mut dest.as_slice();
	while let Some(key) = key_reader.read_next(input).unwrap() {
		decoded.push(key.to_vec());
	}
	assert_eq!(&keys[..], &decoded[..]);
	assert!(input.len() == 0);
}
