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

//! Nodes storage for historied db base implementation.


pub(crate) mod nodes_database {
	use std::sync::Arc;
	use parking_lot::RwLock;
	use crate::DbHash;
	use sp_database::Database;
	use sp_database::Transaction;

	/// Nodes for snapshot db are stored in `STATE_SNAPSHOT`
	/// column (as heads).
	pub(crate) const NODES_COL: u32 = crate::columns::STATE_SNAPSHOT;

	#[derive(Clone)]
	pub(crate) struct DatabasePending {
		// this is limited to changes of nodes of a single value and should be small,
		// therefore we use a simple vec with full scan instead of a map.
		pending: Arc<RwLock<Vec<(Vec<u8>, Option<Vec<u8>>)>>>,
		database: Arc<dyn Database<DbHash>>,
		target_column: u32,
	}

	impl DatabasePending {
		pub(super) fn column(&self) -> u32 {
			self.target_column
		}

		pub(super) fn clear_and_extract_changes(&self) -> Vec<(Vec<u8>, Option<Vec<u8>>)> {
			std::mem::replace(&mut self.pending.write(), Vec::new())
		}

		pub(super) fn apply_transaction(
			&self,
			col: sp_database::ColumnId,
			transaction: &mut Transaction<DbHash>,
		) {
			let pending = self.clear_and_extract_changes();
			for (key, change) in pending {
				if let Some(value) = change {
					transaction.set_from_vec(col, &key, value);
				} else {
					transaction.remove(col, &key);
				}
			}
		}

		pub(super) fn read(&self, col: sp_database::ColumnId, key: &[u8]) -> Option<Vec<u8>> {
			let pending = self.pending.read();
			for kv in pending.iter() {
				match kv.0.as_slice().cmp(key) {
					std::cmp::Ordering::Equal => return kv.1.clone(),
					std::cmp::Ordering::Less => (),
					std::cmp::Ordering::Greater => break,
				}
			}
			self.database.get(col, key)
		}

		fn insert(&self, key: Vec<u8>, value: Option<Vec<u8>>) {
			let mut pending = self.pending.write();
			let mut pos = None;
			let mut mat = None;
			for (i, kv) in pending.iter().enumerate() {
				match kv.0.cmp(&key) {
					std::cmp::Ordering::Equal => {
						mat = Some(i);
						break;
					},
					std::cmp::Ordering::Less => (),
					std::cmp::Ordering::Greater => {
						pos = Some(i);
						break;
					},
				}
			}

			let item = (key, value);
			if let Some(pos) = pos {
				pending.insert(pos, item);
				return;
			}
			if let Some(pos) = mat {
				pending[pos] = item;
				return;
			}
			pending.push(item);
		}

		pub(super) fn write(&self, key: Vec<u8>, value: Vec<u8>) {
			self.insert(key, Some(value))
		}

		pub(super) fn remove(&self, key: Vec<u8>) {
			self.insert(key, None)
		}
	}

	/// Node backend for historied value that need to be
	/// split in backend database.
	///
	/// This is transactional and `apply_transaction` need
	/// to be call to extract changes into an actual db transaction.
	#[derive(Clone)]
	pub struct BlockNodes(pub(crate) DatabasePending);

	/// Branch backend for historied value that need to be
	/// split in backend database.
	///
	/// This is transactional and `apply_transaction` need
	/// to be call to extract changes into an actual db transaction.
	#[derive(Clone)]
	pub struct BranchNodes(pub(crate) DatabasePending);

	impl BlockNodes {
		/// Initialize from clonable pointer to backend database.
		pub fn new(database: Arc<dyn Database<DbHash>>, target_column: u32) -> Self {
			BlockNodes(DatabasePending {
				pending: Arc::new(RwLock::new(Vec::new())),
				database,
				target_column,
			})
		}

		/// Flush pending changes into a database transaction.
		pub fn apply_transaction(&self, transaction: &mut Transaction<DbHash>) {
			self.0.apply_transaction(NODES_COL, transaction)
		}
	}

	impl BranchNodes {
		/// Initialize from clonable pointer to backend database.
		pub fn new(database: Arc<dyn Database<DbHash>>, target_column: u32) -> Self {
			BranchNodes(DatabasePending {
				pending: Arc::new(RwLock::new(Vec::new())),
				database,
				target_column,
			})
		}

		/// Flush pending changes into a database transaction.
		pub fn apply_transaction(&self, transaction: &mut Transaction<DbHash>) {
			self.0.apply_transaction(NODES_COL, transaction)
		}
	}
}

pub(crate) mod nodes_backend {
	use super::nodes_database::{BranchNodes, BlockNodes};
	use historied_db::{
		DecodeWithContext, historied::Value,
		backend::nodes::{NodesMeta, NodeStorage, NodeStorageMut, Node, ContextHead, EstimateSize},
	};
	use codec::{Encode, Decode};

	type StorageFor<V> = <V as Value>::Storage;

	/// Alias for tree context.
	pub type Context = (ContextHead<BranchNodes, ContextHead<BlockNodes, ()>>, ContextHead<BlockNodes, ()>);

	impl<C, M> NodeStorage<C, u64, LinearBackendInner<C>, M> for BlockNodes
		where
			C: Decode,
			M: NodesMeta,
	{
		fn get_node(
			&self,
			reference_key: &[u8],
			parent_encoded_indexes: &[u8],
			relative_index: u64,
		) -> Option<LinearNode<C, M>> {
			let key = <Self as NodeStorage<C, _, _, M>>::vec_address(reference_key, parent_encoded_indexes, relative_index);
			self.0.read(self.0.column(), &key).and_then(|value| {
				// use encoded len as size (this is bigger than the call to estimate size
				// but not really an issue, otherwhise could adjust).
				let reference_len = value.len();

				let input = &mut value.as_slice();
				LinearBackendInner::decode(input).ok().map(|data| Node::new(
					data,
					reference_len,
				))
			})
		}
	}

	impl<C, M> NodeStorageMut<C, u64, LinearBackendInner<C>, M> for BlockNodes
		where
			C: Encode + Decode,
			M: NodesMeta,
	{
		fn set_node(
			&mut self,
			reference_key: &[u8],
			parent_encoded_indexes: &[u8],
			relative_index: u64,
			node: &LinearNode<C, M>,
		) {
			let key = <Self as NodeStorage<C, _, _, M>>::vec_address(reference_key, parent_encoded_indexes, relative_index);
			let encoded = node.inner().encode();
			self.0.write(key, encoded);
		}
		fn remove_node(
			&mut self,
			reference_key: &[u8],
			parent_encoded_indexes: &[u8],
			relative_index: u64,
		) {
			let key = <Self as NodeStorage<C, _, _, M>>::vec_address(reference_key, parent_encoded_indexes, relative_index);
			self.0.remove(key);
		}
	}

	impl<V, M, MB> NodeStorage<BlocksLinear<V, MB>, u32, TreeBackendInner<V, MB>, M> for BranchNodes
		where
			V: Value,
			StorageFor<V>: DecodeWithContext<Context = ()> + EstimateSize,
			M: NodesMeta,
			MB: NodesMeta,
	{
		fn get_node(
			&self,
			reference_key: &[u8],
			parent_encoded_indexes: &[u8],
			relative_index: u64,
		) -> Option<TreeNode<V, M, MB>> {
			let key = <Self as NodeStorage<BlocksLinear<V, MB>, _, _, M>>::vec_address(reference_key, parent_encoded_indexes, relative_index);
			self.0.read(self.0.column(), &key).and_then(|value| {
				// use encoded len as size (this is bigger than the call to estimate size
				// but not an issue, otherwhise could adjust).
				let reference_len = value.len();

				let block_nodes = BlockNodes(self.0.clone());
				let input = &mut value.as_slice();
				TreeBackendInner::decode_with_context(
					input,
					&ContextHead {
						key: reference_key.to_vec(),
						backend: block_nodes,
						encoded_indexes: parent_encoded_indexes.to_vec(),
						node_init_from: (),
					},
				).map(|data| Node::new (
					data,
					reference_len,
				))
			})
		}
	}

	impl<V, M, MB> NodeStorageMut<BlocksLinear<V, MB>, u32, TreeBackendInner<V, MB>, M> for BranchNodes
		where
			V: Value,
			StorageFor<V>: Encode + DecodeWithContext<Context = ()> + EstimateSize,
			M: NodesMeta,
			MB: NodesMeta,
	{
		fn set_node(
			&mut self,
			reference_key: &[u8],
			parent_encoded_indexes: &[u8],
			relative_index: u64,
			node: &TreeNode<V, M, MB>,
		) {
			let key = <Self as NodeStorage<BlocksLinear<V, MB>, _, _, M>>::vec_address(reference_key, parent_encoded_indexes, relative_index);
			let encoded = node.inner().encode();
			self.0.write(key, encoded);
		}
		fn remove_node(
			&mut self,
			reference_key: &[u8],
			parent_encoded_indexes: &[u8],
			relative_index: u64,
		) {
			let key = <Self as NodeStorage<BlocksLinear<V, MB>, _, _, M>>::vec_address(reference_key, parent_encoded_indexes, relative_index);
			self.0.remove(key);
		}
	}

	// Values are stored in memory in Vec like structure
	type LinearBackendInner<C> = historied_db::backend::in_memory::MemoryOnly8<
		C,
		u64,
	>;

	// A multiple nodes wraps multiple vec like structure
	pub(crate) type LinearBackend<C, M> = historied_db::backend::nodes::Head<
		C,
		u64,
		LinearBackendInner<C>,
		M,
		BlockNodes,
		(),
	>;

	// Nodes storing these
	type LinearNode<C, M> = historied_db::backend::nodes::Node<
		C,
		u64,
		LinearBackendInner<C>,
		M,
	>;

	// Branch
	type BlocksLinear<V, M> = historied_db::historied::linear::Linear<V, u64, LinearBackend<StorageFor<V>, M>>;

	// Branch are stored in memory
	type TreeBackendInner<V, M> = historied_db::backend::in_memory::MemoryOnly4<
		BlocksLinear<V, M>,
		u32,
	>;

	// Head of branches
	pub(crate) type TreeBackend<V, M, MB> = historied_db::backend::nodes::Head<
		BlocksLinear<V, MB>,
		u32,
		TreeBackendInner<V, MB>,
		M,
		BranchNodes,
		ContextHead<BlockNodes, ()>
	>;

	// Node with branches
	type TreeNode<V, M, MB> = historied_db::backend::nodes::Node<
		BlocksLinear<V, MB>,
		u32,
		TreeBackendInner<V, MB>,
		M,
	>;
}
