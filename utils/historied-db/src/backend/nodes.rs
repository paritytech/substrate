// This file is part of Substrate.

// Copyright (C) 2020-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Linear backend possibly stored into multiple nodes.

use sp_std::marker::PhantomData;
use sp_std::collections::btree_map::BTreeMap;
use sp_std::cell::RefCell;
use sp_std::vec::Vec;
use sp_std::borrow::Cow;
use super::{LinearStorage};
use crate::historied::HistoriedValue;
use derivative::Derivative;
use crate::{Context, ContextBuilder, InitFrom, DecodeWithContext, Trigger};
#[cfg(feature = "encoded-array-backend")]
use crate::backend::encoded_array::EncodedArrayValue;
use codec::{Encode, Decode, Input};

/// Rough size estimate to manage node size.
pub trait EstimateSize {
	/// For content in Nodes that don't use
	/// `APPLY_SIZE_LIMIT`, set to false.
	const ACTIVE: bool = true;
	/// Return the size estimation.
	/// If `ACTIVE` is set to false this
	/// method can return anything.
	fn estimate_size(&self) -> usize;
}

/// Node storage metadata.
pub trait NodesMeta: Sized + Copy {
	/// If true, and value got an active `EstimateSize`
	/// implementation, then we apply a content size limit,
	/// otherwhise we use the number of node limit.
	const APPLY_SIZE_LIMIT: bool;
	/// The size limit to apply.
	const MAX_NODE_LEN: usize;
	/// Maximum number of items one.
	const MAX_NODE_ITEMS: usize;
	/// Prefix to isolate nodes.
	const STORAGE_PREFIX: &'static [u8];
}

/// Backend storing nodes.
pub trait NodeStorage<V, S, D, M: NodesMeta>: Clone {
	/// Get a node containing a fragement of history.
	///
	/// The scheme uses a relative indexing, the index is only incremented and
	/// should stay valid except if migrating (simplify some concurency questions).
	fn get_node(
		&self,
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_index: u64,
	) -> Option<Node<V, S, D, M>>;

	/// Addressing scheme for key value backend.
	///
	/// This may not be needed (non key value backend will
	/// probably use different strategy), but gives a default
	/// addressing scheme implementation.
	///
	/// Note that this addressing scheme can be replace by a single unique
	/// id store into every `Head`.
	fn vec_address(
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_node_index: u64,
	) -> Vec<u8> {
		let storage_prefix = M::STORAGE_PREFIX;
		let mut result = Vec::with_capacity(
			reference_key.len()
			+ parent_encoded_indexes.len()
			+ storage_prefix.len()
			+ 12);
		result.extend_from_slice(storage_prefix);
		result.extend_from_slice(&(reference_key.len() as u64).to_be_bytes());
		result.extend_from_slice(reference_key);
		result.extend_from_slice(parent_encoded_indexes);
		result.extend_from_slice(&relative_node_index.to_be_bytes());
		result
	}
}

/// Access to node modification.
pub trait NodeStorageMut<V, S, D, M> {
	/// Insert a new node or update value of an existing one.
	///
	/// Same as for `NodeStorage`, addressing is done by `relative_index`.
	/// Note that this change to be effective in the backend might require a call
	/// to `trigger_flush`.
	fn set_node(
		&mut self,
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_index: u64,
		node: &Node<V, S, D, M>,
	);

	/// Remove an existing node.
	///
	/// If node does not exists, just ignore it.
	/// Note that this change is always directly applied.
	/// In case where we delay writting with a flush, the actual removal
	/// only happen on flush (by comparing old indexes used by the head of
	/// this node).
	fn remove_node(
		&mut self,
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_index: u64,
	);
}

// Note that this should not be use out of test, because clones will happen
// many times. It can still be use as primitive for a synch backend with
// inner mutability.
impl<V, S, D: Clone, M: NodesMeta> NodeStorage<V, S, D, M> for BTreeMap<Vec<u8>, Node<V, S, D, M>> {
	fn get_node(
		&self,
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_index: u64,
	) -> Option<Node<V, S, D, M>> {
		let key = Self::vec_address(reference_key, parent_encoded_indexes, relative_index);
		self.get(&key).cloned()
	}
}

impl<V, S, D: Clone, M: NodesMeta> NodeStorageMut<V, S, D, M> for BTreeMap<Vec<u8>, Node<V, S, D, M>> {
	fn set_node(
		&mut self,
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_index: u64,
		node: &Node<V, S, D, M>,
	) {
		let key = Self::vec_address(reference_key, parent_encoded_indexes, relative_index);
		self.insert(key, node.clone());
	}

	fn remove_node(
		&mut self,
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_index: u64,
	) {
		let key = Self::vec_address(reference_key, parent_encoded_indexes, relative_index);
		self.remove(&key);
	}
}

/// Simple example implementation of backend.
#[derive(Clone)]
pub struct InMemoryNoThreadBackend<V, S, D, M>(sp_std::rc::Rc<sp_std::cell::RefCell<BTreeMap<Vec<u8>, Node<V, S, D, M>>>>);

impl<V, S, D, M> InMemoryNoThreadBackend<V, S, D, M> {
	pub fn new() -> Self {
		InMemoryNoThreadBackend(sp_std::rc::Rc::new(sp_std::cell::RefCell::new(BTreeMap::new())))
	}
	#[cfg(test)]
	pub fn inner_len(&self) -> usize {
		self.0.borrow().len()
	}
}

impl<V: Clone, S: Clone, D: Clone, M: NodesMeta> NodeStorage<V, S, D, M> for InMemoryNoThreadBackend<V, S, D, M> {
	fn get_node(
		&self,
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_index: u64,
	) -> Option<Node<V, S, D, M>> {
		let key = Self::vec_address(reference_key, parent_encoded_indexes, relative_index);
		self.0.borrow().get(&key).cloned()
	}
}

impl<V: Clone, S: Clone, D: Clone, M: NodesMeta> NodeStorageMut<V, S, D, M> for InMemoryNoThreadBackend<V, S, D, M> {
	fn set_node(
		&mut self,
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_index: u64,
		node: &Node<V, S, D, M>,
	) {
		let key = Self::vec_address(reference_key, parent_encoded_indexes, relative_index);
		self.0.borrow_mut().insert(key, node.clone());
	}
	fn remove_node(
		&mut self,
		reference_key: &[u8],
		parent_encoded_indexes: &[u8],
		relative_index: u64,
	) {
		let key = Self::vec_address(reference_key, parent_encoded_indexes, relative_index);
		self.0.borrow_mut().remove(&key);
	}
}

#[derive(Derivative)]
#[derivative(Clone(bound="D: Clone"))]
/// A node is a linear backend and some meta information.
pub struct Node<V, S, D, M> {
	/// Inner linear backend of historied values.
	data: D,
	/// If changed, the node needs to be updated in `Head` backend.
	changed: bool,
	/// Keep trace of node byte length for `APPLY_SIZE_LIMIT`.
	reference_len: usize,
	_ph: PhantomData<(V, S, D, M)>,
}

impl<V, S, D, M> Trigger for Node<V, S, D, M>
	where
		D: Trigger,
{
	const TRIGGER: bool = <D as Trigger>::TRIGGER;

	fn trigger_flush(&mut self) {
		if Self::TRIGGER && self.changed {
			self.data.trigger_flush();
		}
	}
}

impl<V, S, D, M> Node<V, S, D, M> {
	/// Access to inner linear data.
	pub fn inner(&self) -> &D {
		&self.data
	}
	/// Instantiate a node from its inner linear data and size.
	pub fn new(data: D, reference_len: usize) -> Self {
		Node {
			data,
			reference_len,
			changed: false,
			_ph: PhantomData::default(),
		}
	}
}

#[derive(Derivative)]
#[derivative(Clone(bound="D: Clone, B: Clone, NI: Clone, V: Clone"))]
/// Head is the entry node, it contains fetched nodes and additional
/// information about this backend state.
pub struct Head<V, S, D, M, B, NI> {
	/// Head contains the last `Node` content.
	inner: Node<V, S, D, M>,
	/// Accessed nodes are kept in memory.
	/// This is a reversed ordered `Vec`, starting at end 'index - 1' and
	/// finishing at most at the very first historied node.
	fetched: RefCell<Vec<Node<V, S, D, M>>>,
	/// Keep trace of initial index start to apply change lazilly.
	old_start_node_index: u64,
	/// Keep trace of initial index end to apply change lazilly.
	old_end_node_index: u64,
	/// The index of the first node, inclusive.
	start_node_index: u64,
	/// The index of the last node, non inclusive (next index to use).
	/// It can also be seen as the head index (but head is not stored
	/// on the node backend).
	end_node_index: u64,
	/// Number of historied values stored in head and all past nodes.
	len: usize,
	/// Backend key used for this head, or any unique identifying key
	/// that we can use to calculate location key of `Node`s from  `Head`.
	reference_key: Vec<u8>,
	/// When stacking multiple head like in `Tree` we store
	/// parent indexes encoded and concatenated (for tree there is only
	/// two levels so it is just encoded index).
	parent_encoded_indexes: Vec<u8>,
	/// All nodes are persisted under this backend storage.
	backend: B,
	/// New node initializing contant.
	node_init_from: NI,
}

#[derive(Encode, Decode)]
/// Codec fragment for head.
struct HeadCodec<'a> {
	/// The index of the first node, inclusive.
	start_node_index: u64,
	/// The index of the last node, non inclusive (next index to use)
	end_node_index: u64,
	/// Number of historied values stored in head and all past nodes.
	len: u64,
	/// The encoded indexes if needed (empty array otherwhise).
	parent_encoded_indexes: Cow<'a, Vec<u8>>,
}

impl<V, S, D, M, B, NI> Encode for Head<V, S, D, M, B, NI>
	where
		D: Encode,
{
	fn size_hint(&self) -> usize {
		self.inner.data.size_hint() + 12
	}

	fn encode_to<T: codec::Output + ?Sized>(&self, dest: &mut T) {
		self.inner.data.encode_to(dest);
		HeadCodec {
			start_node_index: self.start_node_index,
			end_node_index: self.end_node_index,
			len: self.len as u64,
			parent_encoded_indexes: Cow::Borrowed(&self.parent_encoded_indexes),
		}.encode_to(dest)
	}
}

impl<V, S, D, M, B, NI> DecodeWithContext for Head<V, S, D, M, B, NI>
	where
		D: DecodeWithContext<Context = NI> + EstimateSize,
		B: Clone,
		NI: ContextBuilder,
{
	fn decode_with_context<I: Input>(input: &mut I, init: &Self::Context) -> Option<Self> {
		// This contains len from additionaly struct but it is considered
		// negligable.
		let reference_len = match input.remaining_len() {
			Ok(len) => len,
			_ => return None,
		};
		let node_init_from = init.node_init_from.clone();
		D::decode_with_context(input, &init.node_init_from).and_then(|data| {
			let head_decoded = HeadCodec::decode(input).ok();
			head_decoded.map(|head_decoded| {
				let reference_len = reference_len.unwrap_or_else(|| data.estimate_size());
				Head {
					inner: Node::new(data, reference_len),
					fetched: RefCell::new(Vec::new()),
					old_start_node_index: head_decoded.start_node_index,
					old_end_node_index: head_decoded.end_node_index,
					start_node_index: head_decoded.start_node_index,
					end_node_index: head_decoded.end_node_index,
					len: head_decoded.len as usize,
					reference_key: init.key.clone(),
					backend: init.backend.clone(),
					node_init_from,
					parent_encoded_indexes: head_decoded.parent_encoded_indexes.into_owned(),
				}
			})
		})
	}
}

impl<V, S, D, M, B, NI> Head<V, S, D, M, B, NI>
	where
		D: Clone + Trigger,
		M: NodesMeta,
		B: NodeStorage<V, S, D, M> + NodeStorageMut<V, S, D, M>,
{
	/// Changes must always be flushed to be effective.
	/// This is used with `Trigger` `trigger_flush` method.
	fn flush_changes(&mut self, trigger: bool) {
		for d in self.old_start_node_index .. self.start_node_index {
			if trigger {
				if let Some(mut node) = self.backend.get_node(
					&self.reference_key[..],
					&self.parent_encoded_indexes[..],
					d,
				) {
					node.trigger_flush();
				}
			}
			self.backend.remove_node(
				&self.reference_key[..],
				&self.parent_encoded_indexes[..],
				d,
			);
		}
		// this comparison is needed in case we completly clear the initial range,
		// then we avoid deleting nodes that got created.
		let end_node_index = sp_std::cmp::max(self.end_node_index, self.old_start_node_index);
		self.old_start_node_index = self.start_node_index;
		for d in end_node_index .. self.old_end_node_index {
			if trigger {
				if let Some(mut node) = self.backend.get_node(
					&self.reference_key[..],
					&self.parent_encoded_indexes[..],
					d,
				) {
					node.trigger_flush();
				}
			}
			self.backend.remove_node(
				&self.reference_key[..],
				&self.parent_encoded_indexes[..],
				d,
			);
		}
		self.old_end_node_index = self.end_node_index;
		for (index, mut node) in self.fetched.borrow_mut().iter_mut().enumerate() {
			if node.changed {
				if trigger {
					node.trigger_flush();
				}
				self.backend.set_node(
					&self.reference_key[..],
					&self.parent_encoded_indexes[..],
					self.end_node_index - 1 - index as u64,
					node,
				);
				node.changed = false;
			}
		}
	}
}

/// Information needed to initialize a new `Head`.
#[derive(Clone)]
pub struct ContextHead<B, NI> {
	/// The key of the historical value stored in nodes.
	pub key: Vec<u8>,
	/// The encoded indexes (empty Vec for no indexes).
	pub encoded_indexes: Vec<u8>,
	/// The nodes backend.
	pub backend: B,
	/// Int type for internal node content.
	pub node_init_from: NI,
}

impl<B: Clone, NI: ContextBuilder> ContextBuilder for ContextHead<B, NI> {
	const USE_INDEXES: bool = true;

	fn with_indexes(&self, parent_indexes: &[u8], index: &[u8]) -> Self {
		let mut encoded_indexes = parent_indexes.to_vec();
		encoded_indexes.extend_from_slice(index);
		ContextHead {
			key: self.key.clone(),
			backend: self.backend.clone(),
			node_init_from: self.node_init_from.clone(),
			encoded_indexes,
		}
	}

	fn indexes(&self) -> &[u8] {
		self.encoded_indexes.as_slice()
	}
}

impl<V, S, D, M, B, NI> Trigger for Head<V, S, D, M, B, NI>
	where
		D: Clone + Trigger,
		M: NodesMeta,
		B: NodeStorage<V, S, D, M> + NodeStorageMut<V, S, D, M>,
{
	/// Always transmit trigger for fetched nodes and possibly inner data
	/// containing Triggered data.
	const TRIGGER: bool = true;

	fn trigger_flush(&mut self) {
		// first apply to inner data.
		if D::TRIGGER {
			self.inner.trigger_flush();
		}
		self.flush_changes(D::TRIGGER)
	}
}

impl<V, S, D, M, B, NI> Context for Head<V, S, D, M, B, NI>
	where
		D: Context<Context = NI>,
		B: Clone,
		NI: ContextBuilder,
{
	type Context = ContextHead<B, NI>;
}

impl<V, S, D, M, B, NI> InitFrom for Head<V, S, D, M, B, NI>
	where
		D: InitFrom<Context = NI>,
		B: Clone,
		NI: ContextBuilder,
{
	fn init_from(init: Self::Context) -> Self {
		let parent_encoded_indexes = init.indexes().to_vec();
		Head {
			inner: Node {
				data: D::init_from(init.node_init_from.clone()),
				changed: false,
				reference_len: 0,
				_ph: PhantomData,
			},
			fetched: RefCell::new(Vec::new()),
			old_start_node_index: 0,
			old_end_node_index: 0,
			start_node_index: 0,
			end_node_index: 0,
			len: 0,
			reference_key: init.key,
			backend: init.backend,
			node_init_from: init.node_init_from,
			parent_encoded_indexes,
		}
	}
}

impl<V, S, D, M, B, NI> Head<V, S, D, M, B, NI>
	where
		D: LinearStorage<V, S>,
		B: NodeStorage<V, S, D, M>,
		M: NodesMeta,
		S: EstimateSize,
		V: EstimateSize,
		NI: Clone,
{
	// return node index (if node index is end_node_index this is in head),
	// and index in it.
	// Fetch is done backward.
	fn fetch_node(&self, index: usize) -> Option<(usize, usize)> {
		if self.len > index {
			let mut start = self.len as usize - self.inner.data.len();
			if index >= start {
				return Some((self.end_node_index as usize, index - start));
			}
			let mut i = self.end_node_index as usize;
			while i > self.start_node_index as usize {
				i -= 1;
				// fetch_index is 0..(self.end_node_index - self.start_node_index)
				let fetch_index = self.end_node_index as usize - i - 1;
				let has_node = {
					if let Some(node) = self.fetched.borrow().get(fetch_index) {
						start -= node.data.len();
						if index >= start {
							return Some((fetch_index, index - start));
						}
						true
					} else {
						false
					}
				};
				if !has_node {
					if let Some(node) = self.backend.get_node(
						self.reference_key.as_slice(),
						self.parent_encoded_indexes.as_slice(),
						i as u64,
					) {
						start -= node.data.len();
						let r = if index >= start {
							Some((self.fetched.borrow().len(), index - start))
						} else {
							None
						};
						self.fetched.borrow_mut().push(node);

						if r.is_some() {
							return r;
						}
					} else {
						return None;
					}
				}
			}
		}
		None
	}
}

#[cfg(test)]
impl<V, S, D, M, B, NI> Head<V, S, D, M, B, NI>
	where
		D: Clone + Trigger,
		M: NodesMeta,
		B: NodeStorage<V, S, D, M> + NodeStorageMut<V, S, D, M>,
{
	fn clear_fetch_nodes(&mut self) {
		// cannot clear if there is pending changes.
		self.trigger_flush();
		self.fetched.borrow_mut().clear();
	}
}

/// Notice that all max node operation are only for push and pop operation.
/// 'insert' and 'remove' operation would need to use a call to 'realign'
/// operation to rewrite correctly the sizes.
impl<V, S, D, M, B, NI> LinearStorage<V, S> for Head<V, S, D, M, B, NI>
	where
		D: Context<Context = NI> + LinearStorage<V, S>,
		B: NodeStorage<V, S, D, M>,
		M: NodesMeta,
		S: EstimateSize,
		V: EstimateSize + Trigger,
		NI: ContextBuilder,
{
	// Fetched node index (end_node_index is head).
	// If true the node needs to be inserted.
	// Inner node linear storage index.
	type Index = (u64, D::Index);
	fn last(&self) -> Option<Self::Index> {
		if self.len == 0 {
			return None;
		}
		if let Some(inner_index) = self.inner.data.last() {
			return Some((self.end_node_index, inner_index));
		}

		let mut i = self.end_node_index;
		while i > self.start_node_index {
			i -= 1;
			let fetch_index = self.end_node_index - i - 1;
			let inner_index = if let Some(node) = self.fetched.borrow().get(fetch_index as usize) {
				node.data.last()
			} else {
				if let Some(node) = self.backend.get_node(
					self.reference_key.as_slice(),
					self.parent_encoded_indexes.as_slice(),
					i,
				) {
					let inner_index = node.data.last();
					self.fetched.borrow_mut().push(node);
					inner_index
				} else {
					None
				}
			};
			if let Some(inner_index) = inner_index {
				return Some((fetch_index, inner_index));
			}
		}
		None
	}
	fn previous_index(&self, mut index: Self::Index) -> Option<Self::Index> {
		let mut switched = false;
		if index.0 >= self.end_node_index {
			if let Some(inner_index) = self.inner.data.previous_index(index.1) {
				index.1 = inner_index;
				return Some(index);
			} else {
				switched = true;
				index.0 = 0;
			}
		}

		while index.0 + self.start_node_index < self.end_node_index {
			let (try_fetch, inner_index) = if let Some(node) = self.fetched.borrow().get(index.0 as usize) {
				let inner_index = if switched {
					switched = false;
					node.data.last()
				} else {
					node.data.previous_index(index.1)
				};
				(false, inner_index)
			} else {
				(true, None)
			};
			match (try_fetch, inner_index) {
				(true, None) => {
					// could memoize this access.
					if let Some(node) = self.backend.get_node(
						self.reference_key.as_slice(),
						self.parent_encoded_indexes.as_slice(),
						self.end_node_index - 1 - index.0,
					) {
						debug_assert!(switched);
						self.fetched.borrow_mut().push(node);
						continue;
					} else {
						return None;
					}
				},
				(false, None) => {
				},
				(_, Some(inner_index)) => {
					index.1 = inner_index;
					return Some(index);
				},
			}

			index.0 += 1;
			switched = true;
		}
		None
	}
	fn lookup(&self, index: usize) -> Option<Self::Index> {
		self.fetch_node(index).and_then(|(node_index, inner_node_index)| {
			if node_index == self.end_node_index as usize {
				self.inner.data.lookup(inner_node_index).map(|index| (node_index as u64, index))
			} else {
				self.fetched.borrow().get(node_index)
					.and_then(|inner|
					inner.data.lookup(inner_node_index).map(|index| (node_index as u64, index))
				)
			}
		})
	}
	fn len(&self) -> usize {
		self.len
	}
	fn get(&self, index: Self::Index) -> HistoriedValue<V, S> {
		if index.0 == self.end_node_index {
			return self.inner.data.get(index.1)
		}
		self.fetched.borrow()[index.0 as usize].data.get(index.1)
	}
	fn get_state(&self, index: Self::Index) -> S {
		if index.0 == self.end_node_index {
			return self.inner.data.get_state(index.1)
		}
		self.fetched.borrow()[index.0 as usize].data.get_state(index.1)
	}
	fn truncate_until(&mut self, split_off: usize) {
		let i = {
			let mut fetched_mut;
			let (node, i, ix) = match self.fetch_node(split_off) {
				Some((i, ix)) if i >= self.end_node_index as usize =>  {
					(&mut self.inner, i, ix)
				},
				Some((i, ix)) => {
					fetched_mut = self.fetched.borrow_mut();
					if let Some(node) = fetched_mut.get_mut(i) {
						(node, i, ix)
					} else {
						unreachable!("fetch node returns existing index");
					}
				},
				None => {
					return;
				},
			};


			if ix > 0 {
				if M::APPLY_SIZE_LIMIT && V::ACTIVE {
					let mut add_size = 0;
					for i in 0..ix {
						node.data.lookup(i).map(|h| {
							let h = node.data.get(h);
							add_size += h.value.estimate_size() + h.state.estimate_size()
						});
					}
					node.reference_len -= add_size;
				}
				node.changed = true;
				node.data.truncate_until(ix);
			}
			self.start_node_index = if i as u64 == self.end_node_index {
				self.end_node_index
			} else {
				self.end_node_index - i as u64 - 1
			};
			if self.len > split_off {
				self.len -= split_off;
			} else {
				self.len = 0;
			}
			i
		};
		// reversed ordered.
		self.fetched.borrow_mut().truncate(i + 1);
	}
	fn push(&mut self, value: HistoriedValue<V, S>) {
		self.len += 1;
		let mut additional_size: Option<usize> = None;
		
		if !M::APPLY_SIZE_LIMIT || !V::ACTIVE {
			if self.inner.data.len() < M::MAX_NODE_ITEMS {
				self.inner.data.push(value);
				return;
			}
		} else {
			let add_size = value.value.estimate_size() + value.state.estimate_size(); 
			additional_size = Some(add_size);
			// Allow one excess item (in case an item des not fit into the maximum length)
			if self.inner.reference_len < M::MAX_NODE_LEN {
				self.inner.reference_len += add_size;
				self.inner.data.push(value);
				return;
			}
		}

		// New head
		let add_size = additional_size.unwrap_or_else(|| 0);
		self.end_node_index += 1;
		let mut data = D::init_from(self.node_init_from.clone());
		data.push(value);
		let new_node = Node::<V, S, D, M> {
			data,
			changed: true,
			reference_len: add_size,
			_ph: PhantomData,
		};
		self.inner.changed = true;
		let prev = sp_std::mem::replace(&mut self.inner, new_node);
		self.fetched.borrow_mut().insert(0, prev);
	}
	fn insert(&mut self, index: Self::Index, h: HistoriedValue<V, S>) {
		let mut fetched_mut;
		let node = if index.0 == self.end_node_index {
			&mut self.inner
		} else {
			fetched_mut = self.fetched.borrow_mut();
			&mut fetched_mut[index.0 as usize]
		};

		if M::APPLY_SIZE_LIMIT && V::ACTIVE {
			node.reference_len += h.value.estimate_size() + h.state.estimate_size();
		}
		node.changed = true;
		self.len += 1;
		node.data.insert(index.1, h);
	}
	fn remove(&mut self, index: Self::Index) {
		let pop = {
			let mut fetched_mut;
			let (node, first) = if index.0 == self.end_node_index {
				(&mut self.inner, false)
			} else {
				fetched_mut = self.fetched.borrow_mut();
				let len = fetched_mut.len();
				
				(&mut fetched_mut[index.0 as usize], index.0 as usize == len - 1 &&
					len as u64 == self.end_node_index - self.start_node_index)
			};

			node.changed = true;
			self.len -= 1;

			if M::APPLY_SIZE_LIMIT && V::ACTIVE {
				let h = node.data.get(index.1);
				node.reference_len -= h.value.estimate_size() + h.state.estimate_size();
			}
			node.data.remove(index.1);
			first && node.data.len() == 0
		};
		// we don't manage empty head as it will likely be written again.
		// Similarily this could have been skip as we expect truncate until
		// to happen.
		if pop {
			self.start_node_index += 1;
			self.fetched.borrow_mut().pop();
		}
	}
	fn pop(&mut self) -> Option<HistoriedValue<V, S>> {
		if self.len == 0 {
			return None;
		}

		if let Some(h) = self.inner.data.pop() {
			self.len -= 1;
			if self.inner.data.len() > 0 {
				if M::APPLY_SIZE_LIMIT && V::ACTIVE {
					self.inner.reference_len -= h.value.estimate_size() + h.state.estimate_size();
				}
				self.inner.changed = true;
			} else {
				if self.fetched.borrow().len() == 0 {
					if self.len > self.inner.data.len() + 1 {
						self.fetch_node(self.len - self.inner.data.len() - 1);
					}
				}
				if self.fetched.borrow().len() > 0 {
					let removed = self.fetched.borrow_mut().remove(0);
					self.inner = removed;
					self.end_node_index -= 1;
				}
			}

			Some(h)
		} else {
			if self.fetched.borrow().len() == 0 {
				if self.len > self.inner.data.len() + 1 {
					self.fetch_node(self.len - self.inner.data.len() - 1);
				}
			}
			if self.fetched.borrow().len() > 0 {
				let removed = self.fetched.borrow_mut().remove(0);
				self.inner = removed;
				self.end_node_index -= 1;
				self.pop()
			} else {
				None
			}
		}
	}
	fn clear(&mut self) {
		self.start_node_index = 0;
		self.end_node_index = 0;
		self.len = 0;
		self.fetched.borrow_mut().clear();
		self.inner.reference_len = 0;
		self.inner.changed = true;
		self.inner.data.clear();
	}
	fn truncate(&mut self, at: usize) {
		let (in_head, i) = {
			let mut fetched_mut;
			let (node, i, ix, in_head) = match self.fetch_node(at) {
				Some((i, ix)) if i == self.end_node_index as usize =>  {
					(&mut self.inner, i, ix, true)
				},
				Some((i, ix)) => {
					fetched_mut = self.fetched.borrow_mut();
					if let Some(node) = fetched_mut.get_mut(i) {
						(node, i, ix, false)
					} else {
						unreachable!("fetch node returns existing index");
					}
				},
				None => {
					return;
				},
			};

			if ix < node.data.len() {
				if M::APPLY_SIZE_LIMIT && V::ACTIVE {
					let mut add_size = 0;
					for i in ix..node.data.len() {
						node.data.lookup(i).map(|h| {
							let h = node.data.get(h);
							add_size += h.value.estimate_size() + h.state.estimate_size()
						});
					}
					node.reference_len -= add_size;
				}
				node.changed = true;
				node.data.truncate(ix)
			}
			(in_head, i)
		};
		if self.len > at {
			self.len = at;
		}
		// indicates head is empty and all index up to i
		if !in_head {
			let fetch_index = i as u64;
			self.end_node_index -= fetch_index + 1;	
			let mut fetched_mut = self.fetched.borrow_mut();
			// reversed ordered.
			for i in 0..fetch_index + 1 {
				let removed = fetched_mut.remove(0);
				if i == fetch_index {
					self.inner = removed;
				}
			}
			self.inner.changed = true;
		}
	}
	fn emplace(&mut self, index: Self::Index, h: HistoriedValue<V, S>) {
		let mut fetched_mut;
		let node = if index.0 == self.end_node_index {
			&mut self.inner
		} else {
			fetched_mut = self.fetched.borrow_mut();
			&mut fetched_mut[index.0 as usize]
		};

		node.changed = true;

		if M::APPLY_SIZE_LIMIT && V::ACTIVE {
			let h_old = node.data.get(index.1);
			if node.reference_len > h_old.value.estimate_size() + h_old.state.estimate_size() {
				node.reference_len -= h_old.value.estimate_size() + h_old.state.estimate_size();
			} else {
				// we can have biggest estimatition for head (size can be overestimated).
				node.reference_len = 0;
			}
			node.reference_len += h.value.estimate_size() + h.state.estimate_size();
		}
		node.data.emplace(index.1, h);
	}
}

impl EstimateSize for Vec<u8> {
	fn estimate_size(&self) -> usize {
		self.len()
	}
}

impl EstimateSize for u64 {
	fn estimate_size(&self) -> usize {
		8
	}
}

impl EstimateSize for u128 {
	fn estimate_size(&self) -> usize {
		16
	}
}

impl EstimateSize for u32 {
	fn estimate_size(&self) -> usize {
		4
	}
}

impl EstimateSize for u16 {
	fn estimate_size(&self) -> usize {
		2
	}
}

impl<V: EstimateSize> EstimateSize for Option<V> {
	fn estimate_size(&self) -> usize {
		1 + self.as_ref().map(|v| v.estimate_size()).unwrap_or(0)
	}
}

impl<V: EstimateSize, S: EstimateSize> EstimateSize for crate::backend::in_memory::MemoryOnly<V, S> {
	fn estimate_size(&self) -> usize {
		unimplemented!("This should be avoided");
	}
}

impl<D, M, B, NI> AsRef<[u8]> for Head<Vec<u8>, u64, D, M, B, NI>
	where
		D: AsRef<[u8]>,
{
	fn as_ref(&self) -> &[u8] {
		self.inner.data.as_ref()
	}
}

impl<D, M, B, NI> AsMut<[u8]> for Head<Vec<u8>, u64, D, M, B, NI>
	where
		D: AsMut<[u8]>,
{
	fn as_mut(&mut self) -> &mut [u8] {
		self.inner.data.as_mut()
	}
}

impl<V, S, D, M, B, NI> EstimateSize for Head<V, S, D, M, B, NI> {
	fn estimate_size(&self) -> usize {
		self.inner.reference_len
	}
}

impl<V, S, D, M> EstimateSize for Node<V, S, D, M> {
	fn estimate_size(&self) -> usize {
		self.reference_len
	}
}

#[cfg(feature = "encoded-array-backend")]
impl<'a, D, M, B, NI> EncodedArrayValue<'a> for Head<Vec<u8>, u64, D, M, B, NI>
	where
		D: EncodedArrayValue<'a>,
{
	fn from_slice_owned(_slice: &[u8]) -> Self {
		// requires passing around the init item (the key need to be derived): this implementation is needed when we
		// EncodeArrayValue a head that refers to multiple head (those one needs to be instantiated)
		// from_slice & backend + base key. TODO start  by changing from_slice to use a init from
		// param.
		unimplemented!("Require a backend : similar to switch from default to init from, also required to parse meta: using specific size of version would allow fix length meta encode")
	}
	fn from_slice(_slice: &'a [u8]) -> Self {
		unimplemented!("See `from_slice`")
	}
}

#[cfg(test)]
pub(crate) mod test {
	use super::*;

	use crate::backend::in_memory::MemoryOnly;
	#[cfg(feature = "encoded-array-backend")]
	use crate::backend::encoded_array::{EncodedArray, DefaultVersion};

	#[derive(Clone, Copy)]
	pub(crate) struct MetaSize;
	impl NodesMeta for MetaSize {
		const APPLY_SIZE_LIMIT: bool = true;
		const MAX_NODE_LEN: usize = 25;
		const MAX_NODE_ITEMS: usize = 8;
		const STORAGE_PREFIX: &'static [u8] = b"nodesS";
	}
	#[derive(Clone, Copy)]
	pub(crate) struct MetaNb3;
	impl NodesMeta for MetaNb3 {
		const APPLY_SIZE_LIMIT: bool = false;
		const MAX_NODE_LEN: usize = 0;
		const MAX_NODE_ITEMS: usize = 3;
		const STORAGE_PREFIX: &'static [u8] = b"nodes3";
	}
	#[derive(Clone, Copy)]
	pub(crate) struct MetaNb2;
	impl NodesMeta for MetaNb2 {
		const APPLY_SIZE_LIMIT: bool = false;
		const MAX_NODE_LEN: usize = 0;
		const MAX_NODE_ITEMS: usize = 2;
		const STORAGE_PREFIX: &'static [u8] = b"nodes2";
	}
	#[derive(Clone, Copy)]
	pub(crate) struct MetaNb1;
	impl NodesMeta for MetaNb1 {
		const APPLY_SIZE_LIMIT: bool = false;
		const MAX_NODE_LEN: usize = 0;
		const MAX_NODE_ITEMS: usize = 1;
		const STORAGE_PREFIX: &'static [u8] = b"nodes1";
	}

	#[test]
	fn nodes_push_and_query() {
		nodes_push_and_query_inner::<MemoryOnly<Vec<u8>, u64>, MetaSize>();
		nodes_push_and_query_inner::<MemoryOnly<Vec<u8>, u64>, MetaNb3>();
		#[cfg(feature = "encoded-array-backend")]
		nodes_push_and_query_inner::<EncodedArray<Vec<u8>, DefaultVersion>, MetaSize>();
		#[cfg(feature = "encoded-array-backend")]
		nodes_push_and_query_inner::<EncodedArray<Vec<u8>, DefaultVersion>, MetaNb3>();
	}

	fn nodes_push_and_query_inner<D, M>()
		where
			D: InitFrom<Context = ()> + LinearStorage<Vec<u8>, u64> + Clone,
			M: NodesMeta + Clone,
	{
		let init_head = ContextHead {
			backend: BTreeMap::<Vec<u8>, Node<Vec<u8>, u64, D, M>>::new(),
			key: b"any".to_vec(),
			encoded_indexes: Vec::new(),
			node_init_from: (),
		};
		let mut head = Head::<Vec<u8>, u64, D, M, _, _>::init_from(init_head);
		assert_eq!(head.get_state_lookup(0), None);
		for i in 0usize..30 {
			let modu = i % 3;
			head.push(HistoriedValue {
				value: vec![i as u8; 2 + modu],
				state: i as u64,
			});
			for j in 0..i + 1 {
				assert_eq!(head.get_state_lookup(j), Some(j as u64));
			}
			assert_eq!(head.get_state_lookup(i + 1), None);
		}
	}

	#[test]
	fn test_linear_storage() {
		test_linear_storage_inner::<MemoryOnly<Vec<u8>, u64>, MetaSize>();
		test_linear_storage_inner::<MemoryOnly<Vec<u8>, u64>, MetaNb1>();
		test_linear_storage_inner::<MemoryOnly<Vec<u8>, u64>, MetaNb2>();
		test_linear_storage_inner::<MemoryOnly<Vec<u8>, u64>, MetaNb3>();
		#[cfg(feature = "encoded-array-backend")]
		test_linear_storage_inner::<EncodedArray<Vec<u8>, DefaultVersion>, MetaSize>();
		#[cfg(feature = "encoded-array-backend")]
		test_linear_storage_inner::<EncodedArray<Vec<u8>, DefaultVersion>, MetaNb3>();
	}

	fn test_linear_storage_inner<D, M>()
		where
			D: InitFrom<Context = ()> + LinearStorage<Vec<u8>, u64> + Clone,
			M: NodesMeta,
	{
		let init_head = ContextHead {
			backend: BTreeMap::<Vec<u8>, Node<Vec<u8>, u64, D, M>>::new(),
			key: b"any".to_vec(),
			encoded_indexes: Vec::new(),
			node_init_from: (),
		};
		let mut head = Head::<Vec<u8>, u64, D, M, _, _>::init_from(init_head);
		crate::backend::test::test_linear_storage(&mut head);
	}

	#[test]
	fn test_change_with_backend() {
		use crate::Trigger;
		type D = MemoryOnly<Vec<u8>, u64>;
		type M = MetaNb3;
		let backend = InMemoryNoThreadBackend::<Vec<u8>, u64, D, M>::new();
		let init_head = ContextHead {
			backend: backend.clone(),
			key: b"any".to_vec(),
			encoded_indexes: Vec::new(),
			node_init_from: (),
		};
		let mut head = Head::<Vec<u8>, u64, D, M, _, _>::init_from(init_head.clone());
		assert_eq!(backend.0.borrow().len(), 0);
		let push_n = |head: &mut Head::<Vec<u8>, u64, D, M, _, _>, n| {
			for i in 0u8..n {
				head.push(HistoriedValue {
					value: vec![i],
					state: i as u64,
				});
			}
		};
		push_n(&mut head, 3);
		assert_eq!(backend.0.borrow().len(), 0);
		head.trigger_flush();
		// 3 fit in head (meta sized at 3)
		assert_eq!(backend.0.borrow().len(), 0);
		push_n(&mut head, 6);
		assert_eq!(backend.0.borrow().len(), 0);
		head.trigger_flush();
		assert_eq!(backend.0.borrow().len(), 2);

		// first index is fetched node index which is reversed
		let index2 = (1, 1);
		let index3 = (1, 2);
		let index6 = (0, 2);
		// and head is at nb node (not fetched node)
		let index8 = (2, 1);
		let value2 = head.get(index2).value;
		assert_eq!(value2, vec![1]);
		assert_eq!(head.get(index6).value, vec![2]);
		// flushed change
		head.remove(index2);
		head.insert(index2, HistoriedValue{
			value: vec![8],
			state: 8,
		});
		let value2 = head.get(index2).value;
		assert_eq!(value2, vec![8]);
		head.trigger_flush();
		// unflushed one
		head.remove(index3);
		head.insert(index3, HistoriedValue{
			value: vec![9],
			state: 9,
		});
		let value2 = head.get(index2).value;
		assert_eq!(value2, vec![8]);
		let value3 = head.get(index3).value;
		assert_eq!(value3, vec![9]);
		// unflushed but in head
		head.remove(index8);
		head.insert(index8, HistoriedValue{
			value: vec![7],
			state: 7,
		});
		let value8 = head.get(index8).value;
		assert_eq!(value8, vec![7]);

		// encode head and rebuild then query.
		let encoded_head = head.encode();
		head = DecodeWithContext::decode_with_context(&mut encoded_head.as_slice(), &init_head).unwrap();

		assert_eq!(backend.0.borrow_mut().len(), 2);
		// lookup is needed to fetch
		assert_eq!(head.lookup(1), Some(index2));
		let value2 = head.get(index2).value;
		assert_eq!(value2, vec![8]);
		assert_eq!(head.lookup(2), Some(index3));
		let value3 = head.get(index3).value;
		assert_eq!(value3, vec![2]); // original value
		// non need for lookup (in head), still testing
		assert_eq!(head.lookup(7), Some(index8));
		assert_eq!(head.get(index8).value, vec![7]);


		// remove node: size now is 9 - 5 4
		head.truncate_until(5);
		assert_eq!(head.lookup(4), None);
		assert_eq!(head.lookup(5), None);
		let index1 = (0, 0);
		assert_eq!(head.lookup(0), Some(index1));
		// end node index do not change
		let index3 = (2, 1);
		assert_eq!(head.lookup(2), Some(index3));
		assert_eq!(head.get(index1).value, vec![2]); // refer to previous index 6
		assert_eq!(head.get(index3).value, vec![7]); // refer to previous index 8
		assert_eq!(backend.0.borrow().len(), 2);
		head.trigger_flush();
		assert_eq!(backend.0.borrow().len(), 1);
		let encoded_head = head.encode();
		head = DecodeWithContext::decode_with_context(&mut encoded_head.as_slice(), &init_head).unwrap();
		assert_eq!(head.get(index3).value, vec![7]); // refer to previous index 8
		assert_eq!(head.lookup(0), Some(index1)); // non head, fetch
		assert_eq!(head.get(index1).value, vec![2]); // refer to previous index 6
	}

	#[test]
	fn test_change_with_backend_two_levels() {
		use crate::Trigger;
		type BD = MemoryOnly<Vec<u8>, u64>;
		type M = MetaNb3;
		type Backend1 = InMemoryNoThreadBackend::<Vec<u8>, u64, BD, M>;
		type Head1 = Head::<Vec<u8>, u64, BD, M, Backend1, ()>;
		type D = MemoryOnly<Head1, u64>;
		type Backend2 = InMemoryNoThreadBackend::<Head1, u64, D, M>;
		type Head2 = Head::<Head1, u64, D, M, Backend2, ContextHead<Backend1, ()>>;
		let backend1 = Backend1::new();
		let init_head1: ContextHead<Backend1, ()> = ContextHead {
			backend: backend1.clone(),
			key: b"any".to_vec(),
			encoded_indexes: Vec::new(),
			node_init_from: (),
		};
		let backend2 = Backend2::new();
		let init_head2 = ContextHead {
			backend: backend2.clone(),
			key: Vec::new(),
			encoded_indexes: Vec::new(),
			node_init_from: init_head1.clone(),
		};
		let mut head2 = Head2::init_from(init_head2.clone());
		for i in 0u8..9 {
			let mut head1 = Head1::init_from(init_head1.with_indexes(init_head2.indexes(), &[i]));
			for j in 0u8..9 {
				head1.push(HistoriedValue{
					value: vec![j, i],
					state: 8 as u64,
				});
			}
			head2.push(HistoriedValue{
				value: head1,
				state: i as u64,
			});
		}

		assert_eq!(backend1.inner_len(), 0);
		assert_eq!(backend2.inner_len(), 0);
		// query
		for i in 0u8..9 {
			let head1 = head2.get(head2.lookup(i as usize).unwrap()).value;
			for j in 0u8..9 {
				let value = head1.get(head1.lookup(j as usize).unwrap()).value;
				assert_eq!(value, vec![j, i]);
			}
		}

		head2.trigger_flush();
		// 9 size, 3 per nodes - 1 head
		assert_eq!(backend2.inner_len(), 2);
		// (9 size, 3 per nodes - 1 head) * 9
		assert_eq!(backend1.inner_len(), 18);

		head2.clear_fetch_nodes();

		let encoded_head = head2.encode();
		head2 = DecodeWithContext::decode_with_context(&mut encoded_head.as_slice(), &init_head2).unwrap();
		// query
		for i in 0u8..9 {
			let head1 = head2.get(head2.lookup(i as usize).unwrap()).value;
			for j in 0u8..9 {
				let value = head1.get(head1.lookup(j as usize).unwrap()).value;
				assert_eq!(value, vec![j, i]);
			}
		}

		
		// single level 2 rem
		let mut head1 = head2.get(head2.lookup(4).unwrap());
		head1.value.remove(head1.value.lookup(0).unwrap());
		head1.value.remove(head1.value.lookup(0).unwrap());
		head1.value.remove(head1.value.lookup(0).unwrap());
		head2.emplace(head2.lookup(4).unwrap(), head1);
		assert_eq!(backend2.inner_len(), 2);
		assert_eq!(backend1.inner_len(), 18);

		head2.trigger_flush();

		assert_eq!(backend2.inner_len(), 2);
		assert_eq!(backend1.inner_len(), 18 - 1);

		// single level 1 rem
		for i in 0u8..3 {
			let mut head1 = head2.get(head2.lookup(i as usize).unwrap());
			//head1.value.clear();
			for _ in 0u8..9 {
				head1.value.pop();
			}

			// It is responsability of calling code to flush on removal.
			head1.trigger_flush();
		}

		for _ in 0u8..3 {
			// delete these empty heads
			head2.remove(head2.lookup(0 as usize).unwrap());
		}

		head2.trigger_flush();

		assert_eq!(backend2.inner_len(), 1);
		assert_eq!(backend1.inner_len(), 18 - 1 - 6);
	}
}
