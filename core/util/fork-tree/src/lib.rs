// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Utility library for managing tree-like ordered data with logic for pruning
//! the tree while finalizing nodes.

#![warn(missing_docs)]

use std::fmt;
use parity_codec::{Decode, Encode};

/// Error occured when iterating with the tree.
#[derive(Clone, Debug, PartialEq)]
pub enum Error<E> {
	/// Adding duplicate node to tree.
	Duplicate,
	/// Finalizing descendent of tree node without finalizing ancestor(s).
	UnfinalizedAncestor,
	/// Imported or finalized node that is an ancestor of previously finalized node.
	Revert,
	/// Error throw by client when checking for node ancestry.
	Client(E),
}

impl<E: std::error::Error> fmt::Display for Error<E> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		use std::error::Error;
		write!(f, "{}", self.description())
	}
}

impl<E: std::error::Error> std::error::Error for Error<E> {
	fn description(&self) -> &str {
		match *self {
			Error::Duplicate => "Hash already exists in Tree",
			Error::UnfinalizedAncestor => "Finalized descendent of Tree node without finalizing its ancestor(s) first",
			Error::Revert => "Tried to import or finalize node that is an ancestor of a previously finalized node",
			Error::Client(ref err) => err.description(),
		}
	}

	fn cause(&self) -> Option<&std::error::Error> {
		None
	}
}

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

/// A tree data structure that stores several nodes across multiple branches.
/// Top-level branches are called roots. The tree has functionality for
/// finalizing nodes, which means that that node is traversed, and all competing
/// branches are pruned. It also guarantees that nodes in the tree are finalized
/// in order. Each node is uniquely identified by its hash but can be ordered by
/// its number. In order to build the tree an external function must be provided
/// when interacting with the tree to establish a node's ancestry.
#[derive(Clone, Debug, Decode, Encode, PartialEq)]
pub struct ForkTree<H, N, V> {
	roots: Vec<Node<H, N, V>>,
	best_finalized_number: Option<N>,
}

impl<H, N, V> ForkTree<H, N, V> where
	H: PartialEq,
	N: Ord,
{
	/// Create a new empty tree.
	pub fn new() -> ForkTree<H, N, V> {
		ForkTree {
			roots: Vec::new(),
			best_finalized_number: None,
		}
	}

	/// Import a new node into the tree. The given function `is_descendent_of`
	/// should return `true` if the second hash (target) is a descendent of the
	/// first hash (base). This method assumes that nodes in the same branch are
	/// imported in order.
	pub fn import<F, E>(
		&mut self,
		mut hash: H,
		mut number: N,
		mut data: V,
		is_descendent_of: &F,
	) -> Result<bool, Error<E>>
		where E: std::error::Error,
			  F: Fn(&H, &H) -> Result<bool, E>,
	{
		if let Some(ref best_finalized_number) = self.best_finalized_number {
			if number <= *best_finalized_number {
				return Err(Error::Revert);
			}
		}

		for root in self.roots.iter_mut() {
			if root.hash == hash {
				return Err(Error::Duplicate);
			}

			match root.import(hash, number, data, is_descendent_of)? {
				Some((h, n, d)) => {
					hash = h;
					number = n;
					data = d;
				},
				None => return Ok(false),
			}
		}

		self.roots.push(Node {
			data,
			hash: hash,
			number: number,
			children:  Vec::new(),
		});

		Ok(true)
	}

	/// Iterates over the existing roots in the tree.
	pub fn roots(&self) -> impl Iterator<Item=(&H, &N, &V)> {
		self.roots.iter().map(|node| (&node.hash, &node.number, &node.data))
	}

	fn node_iter(&self) -> impl Iterator<Item=&Node<H, N, V>> {
		ForkTreeIterator { stack: self.roots.iter().collect() }
	}

	/// Iterates the nodes in the tree in pre-order.
	pub fn iter(&self) -> impl Iterator<Item=(&H, &N, &V)> {
		self.node_iter().map(|node| (&node.hash, &node.number, &node.data))
	}

	/// Finalize a root in the tree and return it, return `None` in case no root
	/// with the given hash exists. All other roots are pruned, and the children
	/// of the finalized node become the new roots.
	pub fn finalize_root(&mut self, hash: &H) -> Option<V> {
		if let Some(position) = self.roots.iter().position(|node| node.hash == *hash) {
			let node = self.roots.swap_remove(position);
			self.roots = node.children;
			self.best_finalized_number = Some(node.number);
			return Some(node.data);
		}

		None
	}

	/// Finalize a node in the tree. This method will make sure that the node
	/// being finalized is either an existing root (an return its data), or a
	/// node from a competing branch (not in the tree), tree pruning is done
	/// accordingly. The given function `is_descendent_of` should return `true`
	/// if the second hash (target) is a descendent of the first hash (base).
	pub fn finalize<F, E>(
		&mut self,
		hash: &H,
		number: N,
		is_descendent_of: &F,
	) -> Result<FinalizationResult<V>, Error<E>>
		where E: std::error::Error,
			  F: Fn(&H, &H) -> Result<bool, E>
	{
		if let Some(ref best_finalized_number) = self.best_finalized_number {
			if number <= *best_finalized_number {
				return Err(Error::Revert);
			}
		}

		// check if one of the current roots is being finalized
		if let Some(root) = self.finalize_root(hash) {
			return Ok(FinalizationResult::Changed(Some(root)));
		}

		// make sure we're not finalizing a descendent of any root
		for root in self.roots.iter() {
			if number > root.number && is_descendent_of(&root.hash, hash)? {
				return Err(Error::UnfinalizedAncestor);
			}
		}

		// we finalized a block earlier than any existing root (or possibly
		// another fork not part of the tree). make sure to only keep roots that
		// are part of the finalized branch
		let mut changed = false;
		self.roots.retain(|root| {
			let retain = root.number > number && is_descendent_of(hash, &root.hash).unwrap_or(false);

			if !retain {
				changed = true;
			}

			retain
		});

		self.best_finalized_number = Some(number);

		if changed {
			Ok(FinalizationResult::Changed(None))
		} else {
			Ok(FinalizationResult::Unchanged)
		}
	}

	/// Checks if any node in the tree is finalized by either finalizing the
	/// node itself or a child node that's not in the tree, guaranteeing that
	/// the node being finalized isn't a descendent of any of the node's
	/// children. Returns `Some(true)` if the node being finalized is a root,
	/// `Some(false)` if the node being finalized is not a root, and `None` if
	/// no node in the tree is finalized. The given `predicate` is checked on
	/// the prospective finalized root and must pass for finalization to occur.
	/// The given function `is_descendent_of` should return `true` if the second
	/// hash (target) is a descendent of the first hash (base).
	pub fn finalizes_any_with_descendent_if<F, P, E>(
		&self,
		hash: &H,
		number: N,
		is_descendent_of: &F,
		predicate: P,
	) -> Result<Option<bool>, Error<E>>
		where E: std::error::Error,
			  F: Fn(&H, &H) -> Result<bool, E>,
			  P: Fn(&V) -> bool,
	{
		if let Some(ref best_finalized_number) = self.best_finalized_number {
			if number <= *best_finalized_number {
				return Err(Error::Revert);
			}
		}

		// check if the given hash is equal or a descendent of any node in the
		// tree, if we find a valid node that passes the predicate then we must
		// ensure that we're not finalizing past any of its child nodes.
		for node in self.node_iter() {
			if predicate(&node.data) {
				if node.hash == *hash || is_descendent_of(&node.hash, hash)? {
					for node in node.children.iter() {
						if node.number <= number && is_descendent_of(&node.hash, &hash)? {
							return Err(Error::UnfinalizedAncestor);
						}
					}

					return Ok(Some(self.roots.iter().any(|root| root.hash == node.hash)));
				}
			}
		}

		Ok(None)
	}

	/// Finalize a root in the tree by either finalizing the node itself or a
	/// child node that's not in the tree, guaranteeing that the node being
	/// finalized isn't a descendent of any of the root's children. The given
	/// `predicate` is checked on the prospective finalized root and must pass for
	/// finalization to occur. The given function `is_descendent_of` should
	/// return `true` if the second hash (target) is a descendent of the first
	/// hash (base).
	pub fn finalize_with_descendent_if<F, P, E>(
		&mut self,
		hash: &H,
		number: N,
		is_descendent_of: &F,
		predicate: P,
	) -> Result<FinalizationResult<V>, Error<E>>
		where E: std::error::Error,
			  F: Fn(&H, &H) -> Result<bool, E>,
			  P: Fn(&V) -> bool,
	{
		if let Some(ref best_finalized_number) = self.best_finalized_number {
			if number <= *best_finalized_number {
				return Err(Error::Revert);
			}
		}

		// check if the given hash is equal or a a descendent of any root, if we
		// find a valid root that passes the predicate then we must ensure that
		// we're not finalizing past any children node.
		let mut position = None;
		for (i, root) in self.roots.iter().enumerate() {
			if predicate(&root.data) {
				if root.hash == *hash || is_descendent_of(&root.hash, hash)? {
					for node in root.children.iter() {
						if node.number <= number && is_descendent_of(&node.hash, &hash)? {
							return Err(Error::UnfinalizedAncestor);
						}
					}

					position = Some(i);
					break;
				}
			}
		}

		let node_data = position.map(|i| {
			let node = self.roots.swap_remove(i);
			self.roots = node.children;
			self.best_finalized_number = Some(node.number);
			node.data
		});

		// if the block being finalized is earlier than a given root, then it
		// must be its ancestor, otherwise we can prune the root. if there's a
		// root at the same height then the hashes must match. otherwise the
		// node being finalized is higher than the root so it must be its
		// descendent (in this case the node wasn't finalized earlier presumably
		// because the predicate didn't pass).
		let mut changed = false;
		self.roots.retain(|root| {
			let retain =
				root.number > number && is_descendent_of(hash, &root.hash).unwrap_or(false) ||
				root.number == number && root.hash == *hash ||
				is_descendent_of(&root.hash, hash).unwrap_or(false);

			if !retain {
				changed = true;
			}

			retain
		});

		self.best_finalized_number = Some(number);

		match (node_data, changed) {
			(Some(data), _) => Ok(FinalizationResult::Changed(Some(data))),
			(None, true) => Ok(FinalizationResult::Changed(None)),
			(None, false) => Ok(FinalizationResult::Unchanged),
		}
	}
}

// Workaround for: https://github.com/rust-lang/rust/issues/34537
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
		pub fn import<F, E: std::error::Error>(
			&mut self,
			mut hash: H,
			mut number: N,
			mut data: V,
			is_descendent_of: &F,
		) -> Result<Option<(H, N, V)>, Error<E>>
			where E: fmt::Debug,
				  F: Fn(&H, &H) -> Result<bool, E>,
		{
			if self.hash == hash {
				return Err(Error::Duplicate);
			};

			if number <= self.number { return Ok(Some((hash, number, data))); }

			for node in self.children.iter_mut() {
				match node.import(hash, number, data, is_descendent_of)? {
					Some((h, n, d)) => {
						hash = h;
						number = n;
						data = d;
					},
					None => return Ok(None),
				}
			}

			if is_descendent_of(&self.hash, &hash)? {
				self.children.push(Node {
					data,
					hash: hash,
					number: number,
					children: Vec::new(),
				});

				Ok(None)
			} else {
				Ok(Some((hash, number, data)))
			}
		}
	}
}

// Workaround for: https://github.com/rust-lang/rust/issues/34537
use node_implementation::Node;

struct ForkTreeIterator<'a, H, N, V> {
	stack: Vec<&'a Node<H, N, V>>,
}

impl<'a, H, N, V> Iterator for ForkTreeIterator<'a, H, N, V> {
	type Item = &'a Node<H, N, V>;

	fn next(&mut self) -> Option<Self::Item> {
		self.stack.pop().map(|node| {
			self.stack.extend(node.children.iter());
			node
		})
	}
}

#[cfg(test)]
mod test {
	use super::{FinalizationResult, ForkTree, Error};

	#[derive(Debug, PartialEq)]
	struct TestError;

	impl std::fmt::Display for TestError {
		fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
			write!(f, "TestError")
		}
	}

	impl std::error::Error for TestError {}

	fn test_fork_tree<'a>() -> (ForkTree<&'a str, u64, ()>, impl Fn(&&str, &&str) -> Result<bool, TestError>)  {
		let mut tree = ForkTree::new();

		//
		//     - B - C - D - E
		//    /
		//   /   - G
		//  /   /
		// A - F - H - I
		//  \
		//   — J - K
		//
		let is_descendent_of = |base: &&str, block: &&str| -> Result<bool, TestError> {
			let letters = vec!["B", "C", "D", "E", "F", "G", "H", "I", "J", "K"];
			match (*base, *block) {
				("A", b) => Ok(letters.into_iter().any(|n| n == b)),
				("B", b) => Ok(b == "C" || b == "D" || b == "E"),
				("C", b) => Ok(b == "D" || b == "E"),
				("D", b) => Ok(b == "E"),
				("E", _) => Ok(false),
				("F", b) => Ok(b == "G" || b == "H" || b == "I"),
				("G", _) => Ok(false),
				("H", b) => Ok(b == "I"),
				("I", _) => Ok(false),
				("J", b) => Ok(b == "K"),
				("K", _) => Ok(false),
				("0", _) => Ok(true),
				_ => Ok(false),
			}
		};

		tree.import("A", 1, (), &is_descendent_of).unwrap();

		tree.import("B", 2, (), &is_descendent_of).unwrap();
		tree.import("C", 3, (), &is_descendent_of).unwrap();
		tree.import("D", 4, (), &is_descendent_of).unwrap();
		tree.import("E", 5, (), &is_descendent_of).unwrap();

		tree.import("F", 2, (), &is_descendent_of).unwrap();
		tree.import("G", 3, (), &is_descendent_of).unwrap();

		tree.import("H", 3, (), &is_descendent_of).unwrap();
		tree.import("I", 4, (), &is_descendent_of).unwrap();

		tree.import("J", 2, (), &is_descendent_of).unwrap();
		tree.import("K", 3, (), &is_descendent_of).unwrap();

		(tree, is_descendent_of)
	}

	#[test]
	fn import_doesnt_revert() {
		let (mut tree, is_descendent_of) = test_fork_tree();

		tree.finalize_root(&"A");

		assert_eq!(
			tree.best_finalized_number,
			Some(1),
		);

		assert_eq!(
			tree.import("A", 1, (), &is_descendent_of),
			Err(Error::Revert),
		);
	}

	#[test]
	fn import_doesnt_add_duplicates() {
		let (mut tree, is_descendent_of) = test_fork_tree();

		assert_eq!(
			tree.import("A", 1, (), &is_descendent_of),
			Err(Error::Duplicate),
		);

		assert_eq!(
			tree.import("I", 4, (), &is_descendent_of),
			Err(Error::Duplicate),
		);

		assert_eq!(
			tree.import("G", 3, (), &is_descendent_of),
			Err(Error::Duplicate),
		);

		assert_eq!(
			tree.import("K", 3, (), &is_descendent_of),
			Err(Error::Duplicate),
		);
	}

	#[test]
	fn finalize_root_works() {
		let finalize_a = || {
			let (mut tree, ..) = test_fork_tree();

			assert_eq!(
				tree.roots().map(|(h, n, _)| (h.clone(), n.clone())).collect::<Vec<_>>(),
				vec![("A", 1)],
			);

			// finalizing "A" opens up three possible forks
			tree.finalize_root(&"A");

			assert_eq!(
				tree.roots().map(|(h, n, _)| (h.clone(), n.clone())).collect::<Vec<_>>(),
				vec![("B", 2), ("F", 2), ("J", 2)],
			);

			tree
		};

		{
			let mut tree = finalize_a();

			// finalizing "B" will progress on its fork and remove any other competing forks
			tree.finalize_root(&"B");

			assert_eq!(
				tree.roots().map(|(h, n, _)| (h.clone(), n.clone())).collect::<Vec<_>>(),
				vec![("C", 3)],
			);

			// all the other forks have been pruned
			assert!(tree.roots.len() == 1);
		}

		{
			let mut tree = finalize_a();

			// finalizing "J" will progress on its fork and remove any other competing forks
			tree.finalize_root(&"J");

			assert_eq!(
				tree.roots().map(|(h, n, _)| (h.clone(), n.clone())).collect::<Vec<_>>(),
				vec![("K", 3)],
			);

			// all the other forks have been pruned
			assert!(tree.roots.len() == 1);
		}
	}

	#[test]
	fn finalize_works() {
		let (mut tree, is_descendent_of) = test_fork_tree();

		let original_roots = tree.roots.clone();

		// finalizing a block prior to any in the node doesn't change the tree
		assert_eq!(
			tree.finalize(&"0", 0, &is_descendent_of),
			Ok(FinalizationResult::Unchanged),
		);

		assert_eq!(tree.roots, original_roots);

		// finalizing "A" opens up three possible forks
		assert_eq!(
			tree.finalize(&"A", 1, &is_descendent_of),
			Ok(FinalizationResult::Changed(Some(()))),
		);

		assert_eq!(
			tree.roots().map(|(h, n, _)| (h.clone(), n.clone())).collect::<Vec<_>>(),
			vec![("B", 2), ("F", 2), ("J", 2)],
		);

		// finalizing anything lower than what we observed will fail
		assert_eq!(
			tree.best_finalized_number,
			Some(1),
		);

		assert_eq!(
			tree.finalize(&"Z", 1, &is_descendent_of),
			Err(Error::Revert),
		);

		// trying to finalize a node without finalizing its ancestors first will fail
		assert_eq!(
			tree.finalize(&"H", 3, &is_descendent_of),
			Err(Error::UnfinalizedAncestor),
		);

		// after finalizing "F" we can finalize "H"
		assert_eq!(
			tree.finalize(&"F", 2, &is_descendent_of),
			Ok(FinalizationResult::Changed(Some(()))),
		);

		assert_eq!(
			tree.finalize(&"H", 3, &is_descendent_of),
			Ok(FinalizationResult::Changed(Some(()))),
		);

		assert_eq!(
			tree.roots().map(|(h, n, _)| (h.clone(), n.clone())).collect::<Vec<_>>(),
			vec![("I", 4)],
		);

		// finalizing a node from another fork that isn't part of the tree clears the tree
		assert_eq!(
			tree.finalize(&"Z", 5, &is_descendent_of),
			Ok(FinalizationResult::Changed(None)),
		);

		assert!(tree.roots.is_empty());
	}

	#[test]
	fn finalize_with_descendent_works() {
		#[derive(Debug, PartialEq)]
		struct Change { effective: u64 };

		let (mut tree, is_descendent_of) = {
			let mut tree = ForkTree::new();

			let is_descendent_of = |base: &&str, block: &&str| -> Result<bool, TestError> {

				//
				// A0 #1 - (B #2) - (C #5) - D #10 - E #15 - (F #100)
				//                            \
				//                             - (G #100)
				//
				// A1 #1
				//
				// Nodes B, C, F and G  are not part of the tree.
				match (*base, *block) {
					("A0", b) => Ok(b == "B" || b == "C" || b == "D" || b == "G"),
					("A1", _) => Ok(false),
					("C", b) => Ok(b == "D"),
					("D", b) => Ok(b == "E" || b == "F" || b == "G"),
					("E", b) => Ok(b == "F"),
					_ => Ok(false),
				}
			};

			tree.import("A0", 1, Change { effective: 5 }, &is_descendent_of).unwrap();
			tree.import("A1", 1, Change { effective: 5 }, &is_descendent_of).unwrap();
			tree.import("D", 10, Change { effective: 10 }, &is_descendent_of).unwrap();
			tree.import("E", 15, Change { effective: 50 }, &is_descendent_of).unwrap();

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

		// finalizing "D" will finalize a block from the tree, but it can't be applied yet
		// since it is not a root change
		assert_eq!(
			tree.finalizes_any_with_descendent_if(
				&"D",
				10,
				&is_descendent_of,
				|c| c.effective == 10,
			),
			Ok(Some(false)),
		);

		// finalizing "B" doesn't finalize "A0" since the predicate doesn't pass,
		// although it will clear out "A1" from the tree
		assert_eq!(
			tree.finalize_with_descendent_if(
				&"B",
				2,
				&is_descendent_of,
				|c| c.effective <= 2,
			),
			Ok(FinalizationResult::Changed(None)),
		);

		assert_eq!(
			tree.roots().map(|(h, n, _)| (h.clone(), n.clone())).collect::<Vec<_>>(),
			vec![("A0", 1)],
		);

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
			tree.finalize_with_descendent_if(
				&"C",
				5,
				&is_descendent_of,
				|c| c.effective <= 5,
			),
			Ok(FinalizationResult::Changed(Some(Change { effective: 5 }))),
		);

		assert_eq!(
			tree.roots().map(|(h, n, _)| (h.clone(), n.clone())).collect::<Vec<_>>(),
			vec![("D", 10)],
		);

		// finalizing "F" will fail since it would finalize past "E" without finalizing "D" first
		assert_eq!(
			tree.finalizes_any_with_descendent_if(
				&"F",
				100,
				&is_descendent_of,
				|c| c.effective <= 100,
			),
			Err(Error::UnfinalizedAncestor),
		);

		// it will work with "G" though since it is not in the same branch as "E"
		assert_eq!(
			tree.finalizes_any_with_descendent_if(
				&"G",
				100,
				&is_descendent_of,
				|c| c.effective <= 100,
			),
			Ok(Some(true)),
		);

		assert_eq!(
			tree.finalize_with_descendent_if(
				&"G",
				100,
				&is_descendent_of,
				|c| c.effective <= 100,
			),
			Ok(FinalizationResult::Changed(Some(Change { effective: 10 }))),
		);

		// "E" will be pruned out
		assert_eq!(tree.roots().count(), 0);
	}

	#[test]
	fn iter_iterates_in_preorder() {
		let (tree, ..) = test_fork_tree();
		assert_eq!(
			tree.iter().map(|(h, n, _)| (h.clone(), n.clone())).collect::<Vec<_>>(),
			vec![
				("A", 1),
				("J", 2), ("K", 3),
				("F", 2), ("H", 3), ("I", 4),
				("G", 3),
				("B", 2), ("C", 3), ("D", 4), ("E", 5),
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
				tree.finalizes_any_with_descendent_if(
					&"L",
					11,
					&is_descendent_of,
					|i| *i == 10,
				),
				Ok(Some(false)),
			);

			assert_eq!(
				n_is_descendent_of_calls.load(Ordering::SeqCst),
				1,
			);
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
				tree.finalize_with_descendent_if(
					&"L",
					11,
					&is_descendent_of,
					|i| *i == 10,
				),
				Ok(FinalizationResult::Changed(Some(10))),
			);

			assert_eq!(
				n_is_descendent_of_calls.load(Ordering::SeqCst),
				1,
			);
		}
	}
}
