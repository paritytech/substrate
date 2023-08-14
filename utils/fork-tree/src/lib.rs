// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Utility library for managing tree-like ordered data with logic for pruning
//! the tree while finalizing nodes.

#![warn(missing_docs)]

use codec::{Decode, Encode};
use std::{cmp::Reverse, fmt};

/// Error occurred when iterating with the tree.
#[derive(Clone, Debug, PartialEq)]
pub enum Error<E> {
	/// Adding duplicate node to tree.
	Duplicate,
	/// Finalizing descendent of tree node without finalizing ancestor(s).
	UnfinalizedAncestor,
	/// Imported or finalized node that is an ancestor of previously finalized node.
	Revert,
	/// Error thrown by user when checking for node ancestry.
	Client(E),
}

impl<E: std::error::Error> fmt::Display for Error<E> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		let message = match *self {
			Error::Duplicate => "Hash already exists in Tree".into(),
			Error::UnfinalizedAncestor => "Finalized descendent of Tree node without finalizing its ancestor(s) first".into(),
			Error::Revert => "Tried to import or finalize node that is an ancestor of a previously finalized node".into(),
			Error::Client(ref err) => format!("Client error: {}", err),
		};
		write!(f, "{}", message)
	}
}

impl<E: std::error::Error> std::error::Error for Error<E> {}

impl<E: std::error::Error> From<E> for Error<E> {
	fn from(err: E) -> Error<E> {
		Error::Client(err)
	}
}

/// Result of finalizing a node (that could be a part of the tree or not).
#[derive(Debug, PartialEq)]
pub enum FinalizationResult<V> {
	/// The tree has changed, optionally return the value associated with the finalized node.
	Changed(Option<V>),
	/// The tree has not changed.
	Unchanged,
}

/// Filtering action.
#[derive(Debug, PartialEq)]
pub enum FilterAction {
	/// Remove the node and its subtree.
	Remove,
	/// Maintain the node.
	KeepNode,
	/// Maintain the node and its subtree.
	KeepTree,
}

/// A tree data structure that stores several nodes across multiple branches.
///
/// Top-level branches are called roots. The tree has functionality for
/// finalizing nodes, which means that node is traversed, and all competing
/// branches are pruned. It also guarantees that nodes in the tree are finalized
/// in order. Each node is uniquely identified by its hash but can be ordered by
/// its number. In order to build the tree an external function must be provided
/// when interacting with the tree to establish a node's ancestry.
#[derive(Clone, Debug, Decode, Encode, PartialEq)]
pub struct ForkTree<H, N, V> {
	roots: Vec<Node<H, N, V>>,
	best_finalized_number: Option<N>,
}

impl<H, N, V> ForkTree<H, N, V>
where
	H: PartialEq,
	N: Ord,
{
	/// Create a new empty tree instance.
	pub fn new() -> ForkTree<H, N, V> {
		ForkTree { roots: Vec::new(), best_finalized_number: None }
	}

	/// Rebalance the tree.
	///
	/// For each tree level sort child nodes by max branch depth (decreasing).
	///
	/// Most operations in the tree are performed with depth-first search
	/// starting from the leftmost node at every level, since this tree is meant
	/// to be used in a blockchain context, a good heuristic is that the node
	/// we'll be looking for at any point will likely be in one of the deepest chains
	/// (i.e. the longest ones).
	pub fn rebalance(&mut self) {
		self.roots.sort_by_key(|n| Reverse(n.max_depth()));
		let mut stack: Vec<_> = self.roots.iter_mut().collect();
		while let Some(node) = stack.pop() {
			node.children.sort_by_key(|n| Reverse(n.max_depth()));
			stack.extend(node.children.iter_mut());
		}
	}

	/// Import a new node into the tree.
	///
	/// The given function `is_descendent_of` should return `true` if the second
	/// hash (target) is a descendent of the first hash (base).
	///
	/// This method assumes that nodes in the same branch are imported in order.
	///
	/// Returns `true` if the imported node is a root.
	// WARNING: some users of this method (i.e. consensus epoch changes tree) currently silently
	// rely on a **post-order DFS** traversal. If we are using instead a top-down traversal method
	// then the `is_descendent_of` closure, when used after a warp-sync, may end up querying the
	// backend for a block (the one corresponding to the root) that is not present and thus will
	// return a wrong result.
	pub fn import<F, E>(
		&mut self,
		hash: H,
		number: N,
		data: V,
		is_descendent_of: &F,
	) -> Result<bool, Error<E>>
	where
		E: std::error::Error,
		F: Fn(&H, &H) -> Result<bool, E>,
	{
		if let Some(ref best_finalized_number) = self.best_finalized_number {
			if number <= *best_finalized_number {
				return Err(Error::Revert)
			}
		}

		let (children, is_root) =
			match self.find_node_where_mut(&hash, &number, is_descendent_of, &|_| true)? {
				Some(parent) => (&mut parent.children, false),
				None => (&mut self.roots, true),
			};

		if children.iter().any(|elem| elem.hash == hash) {
			return Err(Error::Duplicate)
		}

		children.push(Node { data, hash, number, children: Default::default() });

		if children.len() == 1 {
			// Rebalance may be required only if we've extended the branch depth.
			self.rebalance();
		}

		Ok(is_root)
	}

	/// Iterates over the existing roots in the tree.
	pub fn roots(&self) -> impl Iterator<Item = (&H, &N, &V)> {
		self.roots.iter().map(|node| (&node.hash, &node.number, &node.data))
	}

	fn node_iter(&self) -> impl Iterator<Item = &Node<H, N, V>> {
		// we need to reverse the order of roots to maintain the expected
		// ordering since the iterator uses a stack to track state.
		ForkTreeIterator { stack: self.roots.iter().rev().collect() }
	}

	/// Iterates the nodes in the tree in pre-order.
	pub fn iter(&self) -> impl Iterator<Item = (&H, &N, &V)> {
		self.node_iter().map(|node| (&node.hash, &node.number, &node.data))
	}

	/// Map fork tree into values of new types.
	///
	/// Tree traversal technique (e.g. BFS vs DFS) is left as not specified and
	/// may be subject to change in the future. In other words, your predicates
	/// should not rely on the observed traversal technique currently in use.
	pub fn map<VT, F>(self, f: &mut F) -> ForkTree<H, N, VT>
	where
		F: FnMut(&H, &N, V) -> VT,
	{
		let mut queue: Vec<_> =
			self.roots.into_iter().rev().map(|node| (usize::MAX, node)).collect();
		let mut next_queue = Vec::new();
		let mut output = Vec::new();

		while !queue.is_empty() {
			for (parent_index, node) in queue.drain(..) {
				let new_data = f(&node.hash, &node.number, node.data);
				let new_node = Node {
					hash: node.hash,
					number: node.number,
					data: new_data,
					children: Vec::with_capacity(node.children.len()),
				};

				let node_id = output.len();
				output.push((parent_index, new_node));

				for child in node.children.into_iter().rev() {
					next_queue.push((node_id, child));
				}
			}

			std::mem::swap(&mut queue, &mut next_queue);
		}

		let mut roots = Vec::new();
		while let Some((parent_index, new_node)) = output.pop() {
			if parent_index == usize::MAX {
				roots.push(new_node);
			} else {
				output[parent_index].1.children.push(new_node);
			}
		}

		ForkTree { roots, best_finalized_number: self.best_finalized_number }
	}

	/// Find a node in the tree that is the deepest ancestor of the given
	/// block hash and which passes the given predicate.
	///
	/// The given function `is_descendent_of` should return `true` if the
	/// second hash (target) is a descendent of the first hash (base).
	pub fn find_node_where<F, E, P>(
		&self,
		hash: &H,
		number: &N,
		is_descendent_of: &F,
		predicate: &P,
	) -> Result<Option<&Node<H, N, V>>, Error<E>>
	where
		E: std::error::Error,
		F: Fn(&H, &H) -> Result<bool, E>,
		P: Fn(&V) -> bool,
	{
		let maybe_path = self.find_node_index_where(hash, number, is_descendent_of, predicate)?;
		Ok(maybe_path.map(|path| {
			let children =
				path.iter().take(path.len() - 1).fold(&self.roots, |curr, &i| &curr[i].children);
			&children[path[path.len() - 1]]
		}))
	}

	/// Same as [`find_node_where`](ForkTree::find_node_where), but returns mutable reference.
	pub fn find_node_where_mut<F, E, P>(
		&mut self,
		hash: &H,
		number: &N,
		is_descendent_of: &F,
		predicate: &P,
	) -> Result<Option<&mut Node<H, N, V>>, Error<E>>
	where
		E: std::error::Error,
		F: Fn(&H, &H) -> Result<bool, E>,
		P: Fn(&V) -> bool,
	{
		let maybe_path = self.find_node_index_where(hash, number, is_descendent_of, predicate)?;
		Ok(maybe_path.map(|path| {
			let children = path
				.iter()
				.take(path.len() - 1)
				.fold(&mut self.roots, |curr, &i| &mut curr[i].children);
			&mut children[path[path.len() - 1]]
		}))
	}

	/// Same as [`find_node_where`](ForkTree::find_node_where), but returns indices.
	///
	/// The returned indices represent the full path to reach the matching node starting
	/// from one of the roots, i.e. the earliest index in the traverse path goes first,
	/// and the final index in the traverse path goes last.
	///
	/// If a node is found that matches the predicate the returned path should always
	/// contain at least one index, otherwise `None` is returned.
	//
	// WARNING: some users of this method (i.e. consensus epoch changes tree) currently silently
	// rely on a **post-order DFS** traversal. If we are using instead a top-down traversal method
	// then the `is_descendent_of` closure, when used after a warp-sync, will end up querying the
	// backend for a block (the one corresponding to the root) that is not present and thus will
	// return a wrong result.
	pub fn find_node_index_where<F, E, P>(
		&self,
		hash: &H,
		number: &N,
		is_descendent_of: &F,
		predicate: &P,
	) -> Result<Option<Vec<usize>>, Error<E>>
	where
		E: std::error::Error,
		F: Fn(&H, &H) -> Result<bool, E>,
		P: Fn(&V) -> bool,
	{
		let mut stack = vec![];
		let mut root_idx = 0;
		let mut found = false;
		let mut is_descendent = false;

		while root_idx < self.roots.len() {
			if *number <= self.roots[root_idx].number {
				root_idx += 1;
				continue
			}
			// The second element in the stack tuple tracks what is the **next** children
			// index to search into. If we find an ancestor then we stop searching into
			// alternative branches and we focus on the current path up to the root.
			stack.push((&self.roots[root_idx], 0));
			while let Some((node, i)) = stack.pop() {
				if i < node.children.len() && !is_descendent {
					stack.push((node, i + 1));
					if node.children[i].number < *number {
						stack.push((&node.children[i], 0));
					}
				} else if is_descendent || is_descendent_of(&node.hash, hash)? {
					is_descendent = true;
					if predicate(&node.data) {
						found = true;
						break
					}
				}
			}

			// If the element we are looking for is a descendent of the current root
			// then we can stop the search.
			if is_descendent {
				break
			}
			root_idx += 1;
		}

		Ok(if found {
			// The path is the root index followed by the indices of all the children
			// we were processing when we found the element (remember the stack
			// contains the index of the **next** children to process).
			let path: Vec<_> =
				std::iter::once(root_idx).chain(stack.iter().map(|(_, i)| *i - 1)).collect();
			Some(path)
		} else {
			None
		})
	}

	/// Prune the tree, removing all non-canonical nodes.
	///
	/// We find the node in the tree that is the deepest ancestor of the given hash
	/// and that passes the given predicate. If such a node exists, we re-root the
	/// tree to this node. Otherwise the tree remains unchanged.
	///
	/// The given function `is_descendent_of` should return `true` if the second
	/// hash (target) is a descendent of the first hash (base).
	///
	/// Returns all pruned nodes data.
	pub fn prune<F, E, P>(
		&mut self,
		hash: &H,
		number: &N,
		is_descendent_of: &F,
		predicate: &P,
	) -> Result<impl Iterator<Item = (H, N, V)>, Error<E>>
	where
		E: std::error::Error,
		F: Fn(&H, &H) -> Result<bool, E>,
		P: Fn(&V) -> bool,
	{
		let new_root_path =
			match self.find_node_index_where(hash, number, is_descendent_of, predicate)? {
				Some(path) => path,
				None => return Ok(RemovedIterator { stack: Vec::new() }),
			};

		let mut removed = std::mem::take(&mut self.roots);

		// Find and detach the new root from the removed nodes
		let root_siblings = new_root_path
			.iter()
			.take(new_root_path.len() - 1)
			.fold(&mut removed, |curr, idx| &mut curr[*idx].children);
		let root = root_siblings.remove(new_root_path[new_root_path.len() - 1]);
		self.roots = vec![root];

		// If, because of the `predicate`, the new root is not the deepest ancestor
		// of `hash` then we can remove all the nodes that are descendants of the new
		// `root` but not ancestors of `hash`.
		let mut curr = &mut self.roots[0];
		loop {
			let mut maybe_ancestor_idx = None;
			for (idx, child) in curr.children.iter().enumerate() {
				if child.number < *number && is_descendent_of(&child.hash, hash)? {
					maybe_ancestor_idx = Some(idx);
					break
				}
			}
			let Some(ancestor_idx) = maybe_ancestor_idx else {
				// Now we are positioned just above block identified by `hash`
				break
			};
			// Preserve only the ancestor node, the siblings are removed
			let mut next_siblings = std::mem::take(&mut curr.children);
			let next = next_siblings.remove(ancestor_idx);
			curr.children = vec![next];
			removed.append(&mut next_siblings);
			curr = &mut curr.children[0];
		}

		// Curr now points to our direct ancestor, if necessary remove any node that is
		// not a descendant of `hash`.
		let children = std::mem::take(&mut curr.children);
		for child in children {
			if child.number == *number && child.hash == *hash ||
				*number < child.number && is_descendent_of(hash, &child.hash)?
			{
				curr.children.push(child);
			} else {
				removed.push(child);
			}
		}

		self.rebalance();

		Ok(RemovedIterator { stack: removed })
	}

	/// Finalize a root in the tree and return it, return `None` in case no root
	/// with the given hash exists. All other roots are pruned, and the children
	/// of the finalized node become the new roots.
	pub fn finalize_root(&mut self, hash: &H) -> Option<V> {
		self.roots
			.iter()
			.position(|node| node.hash == *hash)
			.map(|position| self.finalize_root_at(position))
	}

	/// Finalize root at given position. See `finalize_root` comment for details.
	fn finalize_root_at(&mut self, position: usize) -> V {
		let node = self.roots.swap_remove(position);
		self.roots = node.children;
		self.best_finalized_number = Some(node.number);
		node.data
	}

	/// Finalize a node in the tree. This method will make sure that the node
	/// being finalized is either an existing root (and return its data), or a
	/// node from a competing branch (not in the tree), tree pruning is done
	/// accordingly. The given function `is_descendent_of` should return `true`
	/// if the second hash (target) is a descendent of the first hash (base).
	pub fn finalize<F, E>(
		&mut self,
		hash: &H,
		number: N,
		is_descendent_of: &F,
	) -> Result<FinalizationResult<V>, Error<E>>
	where
		E: std::error::Error,
		F: Fn(&H, &H) -> Result<bool, E>,
	{
		if let Some(ref best_finalized_number) = self.best_finalized_number {
			if number <= *best_finalized_number {
				return Err(Error::Revert)
			}
		}

		// check if one of the current roots is being finalized
		if let Some(root) = self.finalize_root(hash) {
			return Ok(FinalizationResult::Changed(Some(root)))
		}

		// make sure we're not finalizing a descendent of any root
		for root in self.roots.iter() {
			if number > root.number && is_descendent_of(&root.hash, hash)? {
				return Err(Error::UnfinalizedAncestor)
			}
		}

		// we finalized a block earlier than any existing root (or possibly
		// another fork not part of the tree). make sure to only keep roots that
		// are part of the finalized branch
		let mut changed = false;
		let roots = std::mem::take(&mut self.roots);

		for root in roots {
			if root.number > number && is_descendent_of(hash, &root.hash)? {
				self.roots.push(root);
			} else {
				changed = true;
			}
		}

		self.best_finalized_number = Some(number);

		if changed {
			Ok(FinalizationResult::Changed(None))
		} else {
			Ok(FinalizationResult::Unchanged)
		}
	}

	/// Finalize a node in the tree and all its ancestors. The given function
	/// `is_descendent_of` should return `true` if the second hash (target) is
	// a descendent of the first hash (base).
	pub fn finalize_with_ancestors<F, E>(
		&mut self,
		hash: &H,
		number: N,
		is_descendent_of: &F,
	) -> Result<FinalizationResult<V>, Error<E>>
	where
		E: std::error::Error,
		F: Fn(&H, &H) -> Result<bool, E>,
	{
		if let Some(ref best_finalized_number) = self.best_finalized_number {
			if number <= *best_finalized_number {
				return Err(Error::Revert)
			}
		}

		// check if one of the current roots is being finalized
		if let Some(root) = self.finalize_root(hash) {
			return Ok(FinalizationResult::Changed(Some(root)))
		}

		// we need to:
		// 1) remove all roots that are not ancestors AND not descendants of finalized block;
		// 2) if node is descendant - just leave it;
		// 3) if node is ancestor - 'open it'
		let mut changed = false;
		let mut idx = 0;
		while idx != self.roots.len() {
			let (is_finalized, is_descendant, is_ancestor) = {
				let root = &self.roots[idx];
				let is_finalized = root.hash == *hash;
				let is_descendant =
					!is_finalized && root.number > number && is_descendent_of(hash, &root.hash)?;
				let is_ancestor = !is_finalized &&
					!is_descendant && root.number < number &&
					is_descendent_of(&root.hash, hash)?;
				(is_finalized, is_descendant, is_ancestor)
			};

			// if we have met finalized root - open it and return
			if is_finalized {
				return Ok(FinalizationResult::Changed(Some(self.finalize_root_at(idx))))
			}

			// if node is descendant of finalized block - just leave it as is
			if is_descendant {
				idx += 1;
				continue
			}

			// if node is ancestor of finalized block - remove it and continue with children
			if is_ancestor {
				let root = self.roots.swap_remove(idx);
				self.roots.extend(root.children);
				changed = true;
				continue
			}

			// if node is neither ancestor, nor descendant of the finalized block - remove it
			self.roots.swap_remove(idx);
			changed = true;
		}

		self.best_finalized_number = Some(number);

		if changed {
			Ok(FinalizationResult::Changed(None))
		} else {
			Ok(FinalizationResult::Unchanged)
		}
	}

	/// Checks if any node in the tree is finalized by either finalizing the
	/// node itself or a node's descendent that's not in the tree, guaranteeing
	/// that the node being finalized isn't a descendent of (or equal to) any of
	/// the node's children. Returns `Some(true)` if the node being finalized is
	/// a root, `Some(false)` if the node being finalized is not a root, and
	/// `None` if no node in the tree is finalized. The given `predicate` is
	/// checked on the prospective finalized root and must pass for finalization
	/// to occur. The given function `is_descendent_of` should return `true` if
	/// the second hash (target) is a descendent of the first hash (base).
	pub fn finalizes_any_with_descendent_if<F, P, E>(
		&self,
		hash: &H,
		number: N,
		is_descendent_of: &F,
		predicate: P,
	) -> Result<Option<bool>, Error<E>>
	where
		E: std::error::Error,
		F: Fn(&H, &H) -> Result<bool, E>,
		P: Fn(&V) -> bool,
	{
		if let Some(ref best_finalized_number) = self.best_finalized_number {
			if number <= *best_finalized_number {
				return Err(Error::Revert)
			}
		}

		// check if the given hash is equal or a descendent of any node in the
		// tree, if we find a valid node that passes the predicate then we must
		// ensure that we're not finalizing past any of its child nodes.
		for node in self.node_iter() {
			if predicate(&node.data) && (node.hash == *hash || is_descendent_of(&node.hash, hash)?)
			{
				for child in node.children.iter() {
					if child.number <= number &&
						(child.hash == *hash || is_descendent_of(&child.hash, hash)?)
					{
						return Err(Error::UnfinalizedAncestor)
					}
				}

				return Ok(Some(self.roots.iter().any(|root| root.hash == node.hash)))
			}
		}

		Ok(None)
	}

	/// Finalize a root in the tree by either finalizing the node itself or a
	/// node's descendent that's not in the tree, guaranteeing that the node
	/// being finalized isn't a descendent of (or equal to) any of the root's
	/// children. The given `predicate` is checked on the prospective finalized
	/// root and must pass for finalization to occur. The given function
	/// `is_descendent_of` should return `true` if the second hash (target) is a
	/// descendent of the first hash (base).
	pub fn finalize_with_descendent_if<F, P, E>(
		&mut self,
		hash: &H,
		number: N,
		is_descendent_of: &F,
		predicate: P,
	) -> Result<FinalizationResult<V>, Error<E>>
	where
		E: std::error::Error,
		F: Fn(&H, &H) -> Result<bool, E>,
		P: Fn(&V) -> bool,
	{
		if let Some(ref best_finalized_number) = self.best_finalized_number {
			if number <= *best_finalized_number {
				return Err(Error::Revert)
			}
		}

		// check if the given hash is equal or a a descendent of any root, if we
		// find a valid root that passes the predicate then we must ensure that
		// we're not finalizing past any children node.
		let mut position = None;
		for (i, root) in self.roots.iter().enumerate() {
			if predicate(&root.data) && (root.hash == *hash || is_descendent_of(&root.hash, hash)?)
			{
				for child in root.children.iter() {
					if child.number <= number &&
						(child.hash == *hash || is_descendent_of(&child.hash, hash)?)
					{
						return Err(Error::UnfinalizedAncestor)
					}
				}

				position = Some(i);
				break
			}
		}

		let node_data = position.map(|i| {
			let node = self.roots.swap_remove(i);
			self.roots = node.children;
			self.best_finalized_number = Some(node.number);
			node.data
		});

		// Retain only roots that are descendents of the finalized block (this
		// happens if the node has been properly finalized) or that are
		// ancestors (or equal) to the finalized block (in this case the node
		// wasn't finalized earlier presumably because the predicate didn't
		// pass).
		let mut changed = false;
		let roots = std::mem::take(&mut self.roots);

		for root in roots {
			let retain = root.number > number && is_descendent_of(hash, &root.hash)? ||
				root.number == number && root.hash == *hash ||
				is_descendent_of(&root.hash, hash)?;

			if retain {
				self.roots.push(root);
			} else {
				changed = true;
			}
		}

		self.best_finalized_number = Some(number);

		match (node_data, changed) {
			(Some(data), _) => Ok(FinalizationResult::Changed(Some(data))),
			(None, true) => Ok(FinalizationResult::Changed(None)),
			(None, false) => Ok(FinalizationResult::Unchanged),
		}
	}

	/// Remove from the tree some nodes (and their subtrees) using a `filter` predicate.
	///
	/// The `filter` is called over tree nodes and returns a filter action:
	/// - `Remove` if the node and its subtree should be removed;
	/// - `KeepNode` if we should maintain the node and keep processing the tree.
	/// - `KeepTree` if we should maintain the node and its entire subtree.
	///
	/// An iterator over all the pruned nodes is returned.
	pub fn drain_filter<F>(&mut self, filter: F) -> impl Iterator<Item = (H, N, V)>
	where
		F: Fn(&H, &N, &V) -> FilterAction,
	{
		let mut removed = vec![];
		let mut retained = Vec::new();

		let mut queue: Vec<_> = std::mem::take(&mut self.roots)
			.into_iter()
			.rev()
			.map(|node| (usize::MAX, node))
			.collect();
		let mut next_queue = Vec::new();

		while !queue.is_empty() {
			for (parent_idx, mut node) in queue.drain(..) {
				match filter(&node.hash, &node.number, &node.data) {
					FilterAction::KeepNode => {
						let node_idx = retained.len();
						let children = std::mem::take(&mut node.children);
						retained.push((parent_idx, node));
						for child in children.into_iter().rev() {
							next_queue.push((node_idx, child));
						}
					},
					FilterAction::KeepTree => {
						retained.push((parent_idx, node));
					},
					FilterAction::Remove => {
						removed.push(node);
					},
				}
			}

			std::mem::swap(&mut queue, &mut next_queue);
		}

		while let Some((parent_idx, node)) = retained.pop() {
			if parent_idx == usize::MAX {
				self.roots.push(node);
			} else {
				retained[parent_idx].1.children.push(node);
			}
		}

		if !removed.is_empty() {
			self.rebalance();
		}
		RemovedIterator { stack: removed }
	}
}

// Workaround for: https://github.com/rust-lang/rust/issues/34537
use node_implementation::Node;

mod node_implementation {
	use super::*;

	#[derive(Clone, Debug, Decode, Encode, PartialEq)]
	pub struct Node<H, N, V> {
		pub hash: H,
		pub number: N,
		pub data: V,
		pub children: Vec<Node<H, N, V>>,
	}

	impl<H: PartialEq, N: Ord, V> Node<H, N, V> {
		/// Finds the max depth among all branches descendent from this node.
		pub fn max_depth(&self) -> usize {
			let mut max: usize = 0;
			let mut stack = vec![(self, 0)];
			while let Some((node, height)) = stack.pop() {
				if height > max {
					max = height;
				}
				node.children.iter().for_each(|n| stack.push((n, height + 1)));
			}
			max
		}
	}
}

struct ForkTreeIterator<'a, H, N, V> {
	stack: Vec<&'a Node<H, N, V>>,
}

impl<'a, H, N, V> Iterator for ForkTreeIterator<'a, H, N, V> {
	type Item = &'a Node<H, N, V>;

	fn next(&mut self) -> Option<Self::Item> {
		self.stack.pop().map(|node| {
			// child nodes are stored ordered by max branch height (decreasing),
			// we want to keep this ordering while iterating but since we're
			// using a stack for iterator state we need to reverse it.
			self.stack.extend(node.children.iter().rev());
			node
		})
	}
}

struct RemovedIterator<H, N, V> {
	stack: Vec<Node<H, N, V>>,
}

impl<H, N, V> Iterator for RemovedIterator<H, N, V> {
	type Item = (H, N, V);

	fn next(&mut self) -> Option<Self::Item> {
		self.stack.pop().map(|mut node| {
			// child nodes are stored ordered by max branch height (decreasing),
			// we want to keep this ordering while iterating but since we're
			// using a stack for iterator state we need to reverse it.
			let children = std::mem::take(&mut node.children);

			self.stack.extend(children.into_iter().rev());
			(node.hash, node.number, node.data)
		})
	}
}

#[cfg(test)]
mod test {
	use crate::FilterAction;

	use super::{Error, FinalizationResult, ForkTree};

	#[derive(Debug, PartialEq)]
	struct TestError;

	impl std::fmt::Display for TestError {
		fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
			write!(f, "TestError")
		}
	}

	impl std::error::Error for TestError {}

	fn test_fork_tree<'a>(
	) -> (ForkTree<&'a str, u64, u32>, impl Fn(&&str, &&str) -> Result<bool, TestError>) {
		let mut tree = ForkTree::new();

		#[rustfmt::skip]
		//
		//     +---B-c-C---D---E
		//     |
		//     |   +---G
		//     |   | 
		// 0---A---F---H---I
		//     |       |
		//     |       +---L-m-M---N
		//     |           |
		//     |           +---O
		//     +---J---K
		//
		// (where N is not a part of fork tree)
		//
		// NOTE: the tree will get automatically rebalance on import and won't be laid out like the
		// diagram above. the children will be ordered by subtree depth and the longest branches
		// will be on the leftmost side of the tree.
		let is_descendent_of = |base: &&str, block: &&str| -> Result<bool, TestError> {
			let letters = vec!["B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O"];
			// This is a trick to have lowercase blocks be direct parents of their
			// uppercase correspondent (A excluded)
			let block = block.to_uppercase();
			match (*base, block) {
				("A", b) => Ok(letters.into_iter().any(|n| n == b)),
				("B" | "c", b) => Ok(b == "C" || b == "D" || b == "E"),
				("C", b) => Ok(b == "D" || b == "E"),
				("D", b) => Ok(b == "E"),
				("E", _) => Ok(false),
				("F", b) =>
					Ok(b == "G" || b == "H" || b == "I" || b == "L" || b == "M" || b == "N" || b == "O"),
				("G", _) => Ok(false),
				("H", b) => Ok(b == "I" || b == "L" || b == "M" || b == "N" || b == "O"),
				("I", _) => Ok(false),
				("J", b) => Ok(b == "K"),
				("K", _) => Ok(false),
				("L", b) => Ok(b == "M" || b == "N" || b == "O"),
				("m", b) => Ok(b == "M" || b == "N"),
				("M", b) => Ok(b == "N"),
				("O", _) => Ok(false),
				("0", _) => Ok(true),
				_ => Ok(false),
			}
		};

		tree.import("A", 10, 1, &is_descendent_of).unwrap();
		tree.import("B", 20, 2, &is_descendent_of).unwrap();
		tree.import("C", 30, 3, &is_descendent_of).unwrap();
		tree.import("D", 40, 4, &is_descendent_of).unwrap();
		tree.import("E", 50, 5, &is_descendent_of).unwrap();
		tree.import("F", 20, 2, &is_descendent_of).unwrap();
		tree.import("G", 30, 3, &is_descendent_of).unwrap();
		tree.import("H", 30, 3, &is_descendent_of).unwrap();
		tree.import("I", 40, 4, &is_descendent_of).unwrap();
		tree.import("L", 40, 4, &is_descendent_of).unwrap();
		tree.import("M", 50, 5, &is_descendent_of).unwrap();
		tree.import("O", 50, 5, &is_descendent_of).unwrap();
		tree.import("J", 20, 2, &is_descendent_of).unwrap();
		tree.import("K", 30, 3, &is_descendent_of).unwrap();

		(tree, is_descendent_of)
	}

	#[test]
	fn import_doesnt_revert() {
		let (mut tree, is_descendent_of) = test_fork_tree();

		tree.finalize_root(&"A");

		assert_eq!(tree.best_finalized_number, Some(10));

		assert_eq!(tree.import("A", 10, 1, &is_descendent_of), Err(Error::Revert));
	}

	#[test]
	fn import_doesnt_add_duplicates() {
		let (mut tree, is_descendent_of) = test_fork_tree();

		assert_eq!(tree.import("A", 10, 1, &is_descendent_of), Err(Error::Duplicate));

		assert_eq!(tree.import("I", 40, 4, &is_descendent_of), Err(Error::Duplicate));

		assert_eq!(tree.import("G", 30, 3, &is_descendent_of), Err(Error::Duplicate));

		assert_eq!(tree.import("K", 30, 3, &is_descendent_of), Err(Error::Duplicate));
	}

	#[test]
	fn finalize_root_works() {
		let finalize_a = || {
			let (mut tree, ..) = test_fork_tree();

			assert_eq!(tree.roots().map(|(h, n, _)| (*h, *n)).collect::<Vec<_>>(), vec![("A", 10)]);

			// finalizing "A" opens up three possible forks
			tree.finalize_root(&"A");

			assert_eq!(
				tree.roots().map(|(h, n, _)| (*h, *n)).collect::<Vec<_>>(),
				vec![("B", 20), ("F", 20), ("J", 20)],
			);

			tree
		};

		{
			let mut tree = finalize_a();

			// finalizing "B" will progress on its fork and remove any other competing forks
			tree.finalize_root(&"B");

			assert_eq!(tree.roots().map(|(h, n, _)| (*h, *n)).collect::<Vec<_>>(), vec![("C", 30)],);

			// all the other forks have been pruned
			assert!(tree.roots.len() == 1);
		}

		{
			let mut tree = finalize_a();

			// finalizing "J" will progress on its fork and remove any other competing forks
			tree.finalize_root(&"J");

			assert_eq!(tree.roots().map(|(h, n, _)| (*h, *n)).collect::<Vec<_>>(), vec![("K", 30)],);

			// all the other forks have been pruned
			assert!(tree.roots.len() == 1);
		}
	}

	#[test]
	fn finalize_works() {
		let (mut tree, is_descendent_of) = test_fork_tree();

		let original_roots = tree.roots.clone();

		// finalizing a block prior to any in the node doesn't change the tree
		assert_eq!(tree.finalize(&"0", 0, &is_descendent_of), Ok(FinalizationResult::Unchanged));

		assert_eq!(tree.roots, original_roots);

		// finalizing "A" opens up three possible forks
		assert_eq!(
			tree.finalize(&"A", 10, &is_descendent_of),
			Ok(FinalizationResult::Changed(Some(1))),
		);

		assert_eq!(
			tree.roots().map(|(h, n, _)| (*h, *n)).collect::<Vec<_>>(),
			vec![("B", 20), ("F", 20), ("J", 20)],
		);

		// finalizing anything lower than what we observed will fail
		assert_eq!(tree.best_finalized_number, Some(10));

		assert_eq!(tree.finalize(&"Z", 10, &is_descendent_of), Err(Error::Revert));

		// trying to finalize a node without finalizing its ancestors first will fail
		assert_eq!(tree.finalize(&"H", 30, &is_descendent_of), Err(Error::UnfinalizedAncestor));

		// after finalizing "F" we can finalize "H"
		assert_eq!(
			tree.finalize(&"F", 20, &is_descendent_of),
			Ok(FinalizationResult::Changed(Some(2))),
		);

		assert_eq!(
			tree.finalize(&"H", 30, &is_descendent_of),
			Ok(FinalizationResult::Changed(Some(3))),
		);

		assert_eq!(
			tree.roots().map(|(h, n, _)| (*h, *n)).collect::<Vec<_>>(),
			vec![("L", 40), ("I", 40)],
		);

		// finalizing a node from another fork that isn't part of the tree clears the tree
		assert_eq!(
			tree.finalize(&"Z", 50, &is_descendent_of),
			Ok(FinalizationResult::Changed(None)),
		);

		assert!(tree.roots.is_empty());
	}

	#[test]
	fn finalize_with_ancestor_works() {
		let (mut tree, is_descendent_of) = test_fork_tree();

		let original_roots = tree.roots.clone();

		// finalizing a block prior to any in the node doesn't change the tree
		assert_eq!(
			tree.finalize_with_ancestors(&"0", 0, &is_descendent_of),
			Ok(FinalizationResult::Unchanged),
		);

		assert_eq!(tree.roots, original_roots);

		// finalizing "A" opens up three possible forks
		assert_eq!(
			tree.finalize_with_ancestors(&"A", 10, &is_descendent_of),
			Ok(FinalizationResult::Changed(Some(1))),
		);

		assert_eq!(
			tree.roots().map(|(h, n, _)| (*h, *n)).collect::<Vec<_>>(),
			vec![("B", 20), ("F", 20), ("J", 20)],
		);

		// finalizing H:
		// 1) removes roots that are not ancestors/descendants of H (B, J)
		// 2) opens root that is ancestor of H (F -> G+H)
		// 3) finalizes the just opened root H (H -> I + L)
		assert_eq!(
			tree.finalize_with_ancestors(&"H", 30, &is_descendent_of),
			Ok(FinalizationResult::Changed(Some(3))),
		);

		assert_eq!(
			tree.roots().map(|(h, n, _)| (*h, *n)).collect::<Vec<_>>(),
			vec![("L", 40), ("I", 40)],
		);

		assert_eq!(tree.best_finalized_number, Some(30));

		// finalizing N (which is not a part of the tree):
		// 1) removes roots that are not ancestors/descendants of N (I)
		// 2) opens root that is ancestor of N (L -> M+O)
		// 3) removes roots that are not ancestors/descendants of N (O)
		// 4) opens root that is ancestor of N (M -> {})
		assert_eq!(
			tree.finalize_with_ancestors(&"N", 60, &is_descendent_of),
			Ok(FinalizationResult::Changed(None)),
		);

		assert_eq!(tree.roots().map(|(h, n, _)| (*h, *n)).collect::<Vec<_>>(), vec![],);

		assert_eq!(tree.best_finalized_number, Some(60));
	}

	#[test]
	fn finalize_with_descendent_works() {
		#[derive(Debug, PartialEq)]
		struct Change {
			effective: u64,
		}

		let (mut tree, is_descendent_of) = {
			let mut tree = ForkTree::new();

			let is_descendent_of = |base: &&str, block: &&str| -> Result<bool, TestError> {
				// A0 #1 - (B #2) - (C #5) - D #10 - E #15 - (F #100)
				//                            \
				//                             - (G #100)
				//
				// A1 #1
				//
				// Nodes B, C, F and G  are not part of the tree.
				match (*base, *block) {
					("A0", b) => Ok(b == "B" || b == "C" || b == "D" || b == "E" || b == "G"),
					("A1", _) => Ok(false),
					("C", b) => Ok(b == "D"),
					("D", b) => Ok(b == "E" || b == "F" || b == "G"),
					("E", b) => Ok(b == "F"),
					_ => Ok(false),
				}
			};

			let is_root = tree.import("A0", 1, Change { effective: 5 }, &is_descendent_of).unwrap();
			assert!(is_root);
			let is_root = tree.import("A1", 1, Change { effective: 5 }, &is_descendent_of).unwrap();
			assert!(is_root);
			let is_root =
				tree.import("D", 10, Change { effective: 10 }, &is_descendent_of).unwrap();
			assert!(!is_root);
			let is_root =
				tree.import("E", 15, Change { effective: 50 }, &is_descendent_of).unwrap();
			assert!(!is_root);

			(tree, is_descendent_of)
		};

		assert_eq!(
			tree.finalizes_any_with_descendent_if(
				&"B",
				2,
				&is_descendent_of,
				|c| c.effective <= 2,
			),
			Ok(None),
		);

		// finalizing "D" is not allowed since it is not a root.
		assert_eq!(
			tree.finalize_with_descendent_if(&"D", 10, &is_descendent_of, |c| c.effective <= 10),
			Err(Error::UnfinalizedAncestor)
		);

		// finalizing "D" will finalize a block from the tree, but it can't be applied yet
		// since it is not a root change.
		assert_eq!(
			tree.finalizes_any_with_descendent_if(&"D", 10, &is_descendent_of, |c| c.effective ==
				10),
			Ok(Some(false)),
		);

		// finalizing "E" is not allowed since there are not finalized anchestors.
		assert_eq!(
			tree.finalizes_any_with_descendent_if(&"E", 15, &is_descendent_of, |c| c.effective ==
				10),
			Err(Error::UnfinalizedAncestor)
		);

		// finalizing "B" doesn't finalize "A0" since the predicate doesn't pass,
		// although it will clear out "A1" from the tree
		assert_eq!(
			tree.finalize_with_descendent_if(&"B", 2, &is_descendent_of, |c| c.effective <= 2),
			Ok(FinalizationResult::Changed(None)),
		);

		assert_eq!(tree.roots().map(|(h, n, _)| (*h, *n)).collect::<Vec<_>>(), vec![("A0", 1)],);

		// finalizing "C" will finalize the node "A0" and prune it out of the tree
		assert_eq!(
			tree.finalizes_any_with_descendent_if(
				&"C",
				5,
				&is_descendent_of,
				|c| c.effective <= 5,
			),
			Ok(Some(true)),
		);

		assert_eq!(
			tree.finalize_with_descendent_if(&"C", 5, &is_descendent_of, |c| c.effective <= 5),
			Ok(FinalizationResult::Changed(Some(Change { effective: 5 }))),
		);

		assert_eq!(tree.roots().map(|(h, n, _)| (*h, *n)).collect::<Vec<_>>(), vec![("D", 10)],);

		// finalizing "F" will fail since it would finalize past "E" without finalizing "D" first
		assert_eq!(
			tree.finalizes_any_with_descendent_if(&"F", 100, &is_descendent_of, |c| c.effective <=
				100,),
			Err(Error::UnfinalizedAncestor),
		);

		// it will work with "G" though since it is not in the same branch as "E"
		assert_eq!(
			tree.finalizes_any_with_descendent_if(&"G", 100, &is_descendent_of, |c| c.effective <=
				100),
			Ok(Some(true)),
		);

		assert_eq!(
			tree.finalize_with_descendent_if(&"G", 100, &is_descendent_of, |c| c.effective <= 100),
			Ok(FinalizationResult::Changed(Some(Change { effective: 10 }))),
		);

		// "E" will be pruned out
		assert_eq!(tree.roots().count(), 0);
	}

	#[test]
	fn iter_iterates_in_preorder() {
		let (tree, ..) = test_fork_tree();
		assert_eq!(
			tree.iter().map(|(h, n, _)| (*h, *n)).collect::<Vec<_>>(),
			vec![
				("A", 10),
				("B", 20),
				("C", 30),
				("D", 40),
				("E", 50),
				("F", 20),
				("H", 30),
				("L", 40),
				("M", 50),
				("O", 50),
				("I", 40),
				("G", 30),
				("J", 20),
				("K", 30),
			],
		);
	}

	#[test]
	fn minimizes_calls_to_is_descendent_of() {
		use std::sync::atomic::{AtomicUsize, Ordering};

		let n_is_descendent_of_calls = AtomicUsize::new(0);

		let is_descendent_of = |_: &&str, _: &&str| -> Result<bool, TestError> {
			n_is_descendent_of_calls.fetch_add(1, Ordering::SeqCst);
			Ok(true)
		};

		{
			// Deep tree where we want to call `finalizes_any_with_descendent_if`. The
			// search for the node should first check the predicate (which is cheaper) and
			// only then call `is_descendent_of`
			let mut tree = ForkTree::new();
			let letters = vec!["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K"];

			for (i, letter) in letters.iter().enumerate() {
				tree.import::<_, TestError>(*letter, i, i, &|_, _| Ok(true)).unwrap();
			}

			// "L" is a descendent of "K", but the predicate will only pass for "K",
			// therefore only one call to `is_descendent_of` should be made
			assert_eq!(
				tree.finalizes_any_with_descendent_if(&"L", 11, &is_descendent_of, |i| *i == 10,),
				Ok(Some(false)),
			);

			assert_eq!(n_is_descendent_of_calls.load(Ordering::SeqCst), 1);
		}

		n_is_descendent_of_calls.store(0, Ordering::SeqCst);

		{
			// Multiple roots in the tree where we want to call `finalize_with_descendent_if`.
			// The search for the root node should first check the predicate (which is cheaper)
			// and only then call `is_descendent_of`
			let mut tree = ForkTree::new();
			let letters = vec!["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K"];

			for (i, letter) in letters.iter().enumerate() {
				tree.import::<_, TestError>(*letter, i, i, &|_, _| Ok(false)).unwrap();
			}

			// "L" is a descendent of "K", but the predicate will only pass for "K",
			// therefore only one call to `is_descendent_of` should be made
			assert_eq!(
				tree.finalize_with_descendent_if(&"L", 11, &is_descendent_of, |i| *i == 10,),
				Ok(FinalizationResult::Changed(Some(10))),
			);

			assert_eq!(n_is_descendent_of_calls.load(Ordering::SeqCst), 1);
		}
	}

	#[test]
	fn map_works() {
		let (mut tree, _) = test_fork_tree();

		// Extend the single root fork-tree to also excercise the roots order during map.
		let is_descendent_of = |_: &&str, _: &&str| -> Result<bool, TestError> { Ok(false) };
		let is_root = tree.import("A1", 10, 1, &is_descendent_of).unwrap();
		assert!(is_root);
		let is_root = tree.import("A2", 10, 1, &is_descendent_of).unwrap();
		assert!(is_root);

		let old_tree = tree.clone();
		let new_tree = tree.map(&mut |hash, _, _| hash.to_owned());

		// Check content and order
		assert!(new_tree.iter().all(|(hash, _, data)| hash == data));
		assert_eq!(
			old_tree.iter().map(|(hash, _, _)| *hash).collect::<Vec<_>>(),
			new_tree.iter().map(|(hash, _, _)| *hash).collect::<Vec<_>>(),
		);
	}

	#[test]
	fn prune_works_for_in_tree_hashes() {
		let (mut tree, is_descendent_of) = test_fork_tree();

		let removed = tree.prune(&"C", &30, &is_descendent_of, &|_| true).unwrap();

		assert_eq!(tree.roots.iter().map(|node| node.hash).collect::<Vec<_>>(), vec!["B"]);

		assert_eq!(
			tree.iter().map(|(hash, _, _)| *hash).collect::<Vec<_>>(),
			vec!["B", "C", "D", "E"],
		);

		assert_eq!(
			removed.map(|(hash, _, _)| hash).collect::<Vec<_>>(),
			vec!["A", "F", "H", "L", "M", "O", "I", "G", "J", "K"]
		);

		let removed = tree.prune(&"E", &50, &is_descendent_of, &|_| true).unwrap();

		assert_eq!(tree.roots.iter().map(|node| node.hash).collect::<Vec<_>>(), vec!["D"]);

		assert_eq!(tree.iter().map(|(hash, _, _)| *hash).collect::<Vec<_>>(), vec!["D", "E"]);

		assert_eq!(removed.map(|(hash, _, _)| hash).collect::<Vec<_>>(), vec!["B", "C"]);
	}

	#[test]
	fn prune_works_for_out_of_tree_hashes() {
		let (mut tree, is_descendent_of) = test_fork_tree();

		let removed = tree.prune(&"c", &25, &is_descendent_of, &|_| true).unwrap();

		assert_eq!(tree.roots.iter().map(|node| node.hash).collect::<Vec<_>>(), vec!["B"]);

		assert_eq!(
			tree.iter().map(|(hash, _, _)| *hash).collect::<Vec<_>>(),
			vec!["B", "C", "D", "E"],
		);

		assert_eq!(
			removed.map(|(hash, _, _)| hash).collect::<Vec<_>>(),
			vec!["A", "F", "H", "L", "M", "O", "I", "G", "J", "K"]
		);
	}

	#[test]
	fn prune_works_for_not_direct_ancestor() {
		let (mut tree, is_descendent_of) = test_fork_tree();

		// This is to re-root the tree not at the immediate ancestor, but the one just before.
		let removed = tree.prune(&"m", &45, &is_descendent_of, &|height| *height == 3).unwrap();

		assert_eq!(tree.roots.iter().map(|node| node.hash).collect::<Vec<_>>(), vec!["H"]);

		assert_eq!(tree.iter().map(|(hash, _, _)| *hash).collect::<Vec<_>>(), vec!["H", "L", "M"],);

		assert_eq!(
			removed.map(|(hash, _, _)| hash).collect::<Vec<_>>(),
			vec!["O", "I", "A", "B", "C", "D", "E", "F", "G", "J", "K"]
		);
	}

	#[test]
	fn prune_works_for_far_away_ancestor() {
		let (mut tree, is_descendent_of) = test_fork_tree();

		let removed = tree.prune(&"m", &45, &is_descendent_of, &|height| *height == 2).unwrap();

		assert_eq!(tree.roots.iter().map(|node| node.hash).collect::<Vec<_>>(), vec!["F"]);

		assert_eq!(
			tree.iter().map(|(hash, _, _)| *hash).collect::<Vec<_>>(),
			vec!["F", "H", "L", "M"],
		);

		assert_eq!(
			removed.map(|(hash, _, _)| hash).collect::<Vec<_>>(),
			vec!["O", "I", "G", "A", "B", "C", "D", "E", "J", "K"]
		);
	}

	#[test]
	fn find_node_backtracks_after_finding_highest_descending_node() {
		let mut tree = ForkTree::new();

		// A - B
		//  \
		//   — C
		//
		let is_descendent_of = |base: &&str, block: &&str| -> Result<bool, TestError> {
			match (*base, *block) {
				("A", b) => Ok(b == "B" || b == "C" || b == "D"),
				("B", b) | ("C", b) => Ok(b == "D"),
				("0", _) => Ok(true),
				_ => Ok(false),
			}
		};

		tree.import("A", 1, 1, &is_descendent_of).unwrap();
		tree.import("B", 2, 2, &is_descendent_of).unwrap();
		tree.import("C", 2, 4, &is_descendent_of).unwrap();

		// when searching the tree we reach node `C`, but the
		// predicate doesn't pass. we should backtrack to `B`, but not to `A`,
		// since "B" fulfills the predicate.
		let node = tree.find_node_where(&"D", &3, &is_descendent_of, &|data| *data < 3).unwrap();

		assert_eq!(node.unwrap().hash, "B");
	}

	#[test]
	fn rebalance_works() {
		let (mut tree, _) = test_fork_tree();

		// the tree is automatically rebalanced on import, therefore we should iterate in preorder
		// exploring the longest forks first. check the ascii art above to understand the expected
		// output below.
		assert_eq!(
			tree.iter().map(|(h, _, _)| *h).collect::<Vec<_>>(),
			vec!["A", "B", "C", "D", "E", "F", "H", "L", "M", "O", "I", "G", "J", "K"],
		);

		// let's add a block "P" which is a descendent of block "O"
		let is_descendent_of = |base: &&str, block: &&str| -> Result<bool, TestError> {
			match (*base, *block) {
				(b, "P") => Ok(vec!["A", "F", "H", "L", "O"].into_iter().any(|n| n == b)),
				_ => Ok(false),
			}
		};

		tree.import("P", 60, 6, &is_descendent_of).unwrap();

		// this should re-order the tree, since the branch "A -> B -> C -> D -> E" is no longer tied
		// with 5 blocks depth. additionally "O" should be visited before "M" now, since it has one
		// descendent "P" which makes that branch 6 blocks long.
		assert_eq!(
			tree.iter().map(|(h, _, _)| *h).collect::<Vec<_>>(),
			["A", "F", "H", "L", "O", "P", "M", "I", "G", "B", "C", "D", "E", "J", "K"]
		);
	}

	#[test]
	fn drain_filter_works() {
		let (mut tree, _) = test_fork_tree();

		let filter = |h: &&str, _: &u64, _: &u32| match *h {
			"A" | "B" | "F" | "G" => FilterAction::KeepNode,
			"C" => FilterAction::KeepTree,
			"H" | "J" => FilterAction::Remove,
			_ => panic!("Unexpected filtering for node: {}", *h),
		};

		let removed = tree.drain_filter(filter);

		assert_eq!(
			tree.iter().map(|(h, _, _)| *h).collect::<Vec<_>>(),
			["A", "B", "C", "D", "E", "F", "G"]
		);

		assert_eq!(
			removed.map(|(h, _, _)| h).collect::<Vec<_>>(),
			["H", "L", "M", "O", "I", "J", "K"]
		);
	}

	#[test]
	fn find_node_index_works() {
		let (tree, is_descendent_of) = test_fork_tree();

		let path = tree
			.find_node_index_where(&"D", &40, &is_descendent_of, &|_| true)
			.unwrap()
			.unwrap();
		assert_eq!(path, [0, 0, 0]);

		let path = tree
			.find_node_index_where(&"O", &50, &is_descendent_of, &|_| true)
			.unwrap()
			.unwrap();
		assert_eq!(path, [0, 1, 0, 0]);

		let path = tree
			.find_node_index_where(&"N", &60, &is_descendent_of, &|_| true)
			.unwrap()
			.unwrap();
		assert_eq!(path, [0, 1, 0, 0, 0]);
	}

	#[test]
	fn find_node_index_with_predicate_works() {
		let is_descendent_of = |parent: &char, child: &char| match *parent {
			'A' => Ok(['B', 'C', 'D', 'E', 'F'].contains(child)),
			'B' => Ok(['C', 'D'].contains(child)),
			'C' => Ok(['D'].contains(child)),
			'E' => Ok(['F'].contains(child)),
			'D' | 'F' => Ok(false),
			_ => Err(TestError),
		};

		// A(t) --- B(f) --- C(t) --- D(f)
		//      \-- E(t) --- F(f)
		let mut tree: ForkTree<char, u8, bool> = ForkTree::new();
		tree.import('A', 1, true, &is_descendent_of).unwrap();
		tree.import('B', 2, false, &is_descendent_of).unwrap();
		tree.import('C', 3, true, &is_descendent_of).unwrap();
		tree.import('D', 4, false, &is_descendent_of).unwrap();

		tree.import('E', 2, true, &is_descendent_of).unwrap();
		tree.import('F', 3, false, &is_descendent_of).unwrap();

		let path = tree
			.find_node_index_where(&'D', &4, &is_descendent_of, &|&value| !value)
			.unwrap()
			.unwrap();
		assert_eq!(path, [0, 0]);

		let path = tree
			.find_node_index_where(&'D', &4, &is_descendent_of, &|&value| value)
			.unwrap()
			.unwrap();
		assert_eq!(path, [0, 0, 0]);

		let path = tree
			.find_node_index_where(&'F', &3, &is_descendent_of, &|&value| !value)
			.unwrap();
		assert_eq!(path, None);

		let path = tree
			.find_node_index_where(&'F', &3, &is_descendent_of, &|&value| value)
			.unwrap()
			.unwrap();
		assert_eq!(path, [0, 1]);
	}

	#[test]
	fn find_node_works() {
		let (tree, is_descendent_of) = test_fork_tree();

		let node = tree.find_node_where(&"B", &20, &is_descendent_of, &|_| true).unwrap().unwrap();
		assert_eq!((node.hash, node.number), ("A", 10));

		let node = tree.find_node_where(&"D", &40, &is_descendent_of, &|_| true).unwrap().unwrap();
		assert_eq!((node.hash, node.number), ("C", 30));

		let node = tree.find_node_where(&"O", &50, &is_descendent_of, &|_| true).unwrap().unwrap();
		assert_eq!((node.hash, node.number), ("L", 40));

		let node = tree.find_node_where(&"N", &60, &is_descendent_of, &|_| true).unwrap().unwrap();
		assert_eq!((node.hash, node.number), ("M", 50));
	}

	#[test]
	fn post_order_traversal_requirement() {
		let (mut tree, is_descendent_of) = test_fork_tree();

		// Test for the post-order DFS traversal requirement as specified by the
		// `find_node_index_where` and `import` comments.
		let is_descendent_of_for_post_order = |parent: &&str, child: &&str| match *parent {
			"A" => Err(TestError),
			"K" if *child == "Z" => Ok(true),
			_ => is_descendent_of(parent, child),
		};

		// Post order traversal requirement for `find_node_index_where`
		let path = tree
			.find_node_index_where(&"N", &60, &is_descendent_of_for_post_order, &|_| true)
			.unwrap()
			.unwrap();
		assert_eq!(path, [0, 1, 0, 0, 0]);

		// Post order traversal requirement for `import`
		let res = tree.import(&"Z", 100, 10, &is_descendent_of_for_post_order);
		assert_eq!(res, Ok(false));
		assert_eq!(
			tree.iter().map(|node| *node.0).collect::<Vec<_>>(),
			vec!["A", "B", "C", "D", "E", "F", "H", "L", "M", "O", "I", "G", "J", "K", "Z"],
		);
	}
}
