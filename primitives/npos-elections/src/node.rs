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

//! (very) Basic implementation of a graph node used in the reduce algorithm.

use sp_std::{cell::RefCell, fmt, prelude::*, rc::Rc};

/// The role that a node can accept.
#[derive(PartialEq, Eq, Ord, PartialOrd, Clone, Debug)]
pub(crate) enum NodeRole {
	/// A voter. This is synonym to a nominator in a staking context.
	Voter,
	/// A target. This is synonym to a candidate/validator in a staking context.
	Target,
}

pub(crate) type RefCellOf<T> = Rc<RefCell<T>>;
pub(crate) type NodeRef<A> = RefCellOf<Node<A>>;

/// Identifier of a node. This is particularly handy to have a proper `PartialEq` implementation.
/// Otherwise, self votes wouldn't have been indistinguishable.
#[derive(PartialOrd, Ord, Clone, PartialEq, Eq)]
pub(crate) struct NodeId<A> {
	/// An account-like identifier representing the node.
	pub who: A,
	/// The role of the node.
	pub role: NodeRole,
}

impl<A> NodeId<A> {
	/// Create a new [`NodeId`].
	pub fn from(who: A, role: NodeRole) -> Self {
		Self { who, role }
	}
}

#[cfg(feature = "std")]
impl<A: fmt::Debug> sp_std::fmt::Debug for NodeId<A> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> sp_std::fmt::Result {
		write!(
			f,
			"Node({:?}, {:?})",
			self.who,
			if self.role == NodeRole::Voter { "V" } else { "T" }
		)
	}
}

/// A one-way graph note. This can only store a pointer to its parent.
#[derive(Clone)]
pub(crate) struct Node<A> {
	/// The identifier of the note.
	pub(crate) id: NodeId<A>,
	/// The parent pointer.
	pub(crate) parent: Option<NodeRef<A>>,
}

impl<A: PartialEq> PartialEq for Node<A> {
	fn eq(&self, other: &Node<A>) -> bool {
		self.id == other.id
	}
}

impl<A: PartialEq> Eq for Node<A> {}

#[cfg(feature = "std")]
impl<A: fmt::Debug + Clone> fmt::Debug for Node<A> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "({:?} --> {:?})", self.id, self.parent.as_ref().map(|p| p.borrow().id.clone()))
	}
}

impl<A: PartialEq + Eq + Clone + fmt::Debug> Node<A> {
	/// Create a new [`Node`]
	pub fn new(id: NodeId<A>) -> Node<A> {
		Self { id, parent: None }
	}

	/// Returns true if `other` is the parent of `who`.
	pub fn is_parent_of(who: &NodeRef<A>, other: &NodeRef<A>) -> bool {
		if who.borrow().parent.is_none() {
			return false
		}
		who.borrow().parent.as_ref() == Some(other)
	}

	/// Removes the parent of `who`.
	pub fn remove_parent(who: &NodeRef<A>) {
		who.borrow_mut().parent = None;
	}

	/// Sets `who`'s parent to be `parent`.
	pub fn set_parent_of(who: &NodeRef<A>, parent: &NodeRef<A>) {
		who.borrow_mut().parent = Some(parent.clone());
	}

	/// Finds the root of `start`. It return a tuple of `(root, root_vec)` where `root_vec` is the
	/// vector of Nodes leading to the root. Hence the first element is the start itself and the
	/// last one is the root. As convenient, the root itself is also returned as the first element
	/// of the tuple.
	///
	/// This function detects cycles and breaks as soon a duplicate node is visited, returning the
	/// cycle up to but not including the duplicate node.
	///
	/// If you are certain that no cycles exist, you can use [`root_unchecked`].
	pub fn root(start: &NodeRef<A>) -> (NodeRef<A>, Vec<NodeRef<A>>) {
		let mut parent_path: Vec<NodeRef<A>> = Vec::new();
		let mut visited: Vec<NodeRef<A>> = Vec::new();

		parent_path.push(start.clone());
		visited.push(start.clone());
		let mut current = start.clone();

		while let Some(ref next_parent) = current.clone().borrow().parent {
			if visited.contains(next_parent) {
				break
			}
			parent_path.push(next_parent.clone());
			current = next_parent.clone();
			visited.push(current.clone());
		}

		(current, parent_path)
	}

	/// Consumes self and wraps it in a `Rc<RefCell<T>>`. This type can be used as the pointer type
	/// to a parent node.
	pub fn into_ref(self) -> NodeRef<A> {
		Rc::from(RefCell::from(self))
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	fn id(i: u32) -> NodeId<u32> {
		NodeId::from(i, NodeRole::Target)
	}

	#[test]
	fn basic_create_works() {
		let node = Node::new(id(10));
		assert_eq!(node, Node { id: NodeId { who: 10, role: NodeRole::Target }, parent: None });
	}

	#[test]
	fn set_parent_works() {
		let a = Node::new(id(10)).into_ref();
		let b = Node::new(id(20)).into_ref();

		assert_eq!(a.borrow().parent, None);
		Node::set_parent_of(&a, &b);
		assert_eq!(*a.borrow().parent.as_ref().unwrap(), b);
	}

	#[test]
	fn get_root_singular() {
		let a = Node::new(id(1)).into_ref();
		assert_eq!(Node::root(&a), (a.clone(), vec![a.clone()]));
	}

	#[test]
	fn get_root_works() {
		// 	D <-- A <-- B <-- C
		// 			\
		// 			 <-- E
		let a = Node::new(id(1)).into_ref();
		let b = Node::new(id(2)).into_ref();
		let c = Node::new(id(3)).into_ref();
		let d = Node::new(id(4)).into_ref();
		let e = Node::new(id(5)).into_ref();
		let f = Node::new(id(6)).into_ref();

		Node::set_parent_of(&c, &b);
		Node::set_parent_of(&b, &a);
		Node::set_parent_of(&e, &a);
		Node::set_parent_of(&a, &d);

		assert_eq!(Node::root(&e), (d.clone(), vec![e.clone(), a.clone(), d.clone()]));

		assert_eq!(Node::root(&a), (d.clone(), vec![a.clone(), d.clone()]));

		assert_eq!(Node::root(&c), (d.clone(), vec![c.clone(), b.clone(), a.clone(), d.clone()]));

		// 	D 	    A <-- B <-- C
		// 	F <-- /	\
		// 			 <-- E
		Node::set_parent_of(&a, &f);

		assert_eq!(Node::root(&a), (f.clone(), vec![a.clone(), f.clone()]));

		assert_eq!(Node::root(&c), (f.clone(), vec![c.clone(), b.clone(), a.clone(), f.clone()]));
	}

	#[test]
	fn get_root_on_cycle() {
		// A ---> B
		// |      |
		//  <---- C
		let a = Node::new(id(1)).into_ref();
		let b = Node::new(id(2)).into_ref();
		let c = Node::new(id(3)).into_ref();

		Node::set_parent_of(&a, &b);
		Node::set_parent_of(&b, &c);
		Node::set_parent_of(&c, &a);

		let (root, path) = Node::root(&a);
		assert_eq!(root, c);
		assert_eq!(path.clone(), vec![a.clone(), b.clone(), c.clone()]);
	}

	#[test]
	fn get_root_on_cycle_2() {
		// A ---> B
		// |   |  |
		//     - C
		let a = Node::new(id(1)).into_ref();
		let b = Node::new(id(2)).into_ref();
		let c = Node::new(id(3)).into_ref();

		Node::set_parent_of(&a, &b);
		Node::set_parent_of(&b, &c);
		Node::set_parent_of(&c, &b);

		let (root, path) = Node::root(&a);
		assert_eq!(root, c);
		assert_eq!(path.clone(), vec![a.clone(), b.clone(), c.clone()]);
	}

	#[test]
	fn node_cmp_stack_overflows_on_non_unique_elements() {
		// To make sure we don't stack overflow on duplicate who. This needs manual impl of
		// PartialEq.
		let a = Node::new(id(1)).into_ref();
		let b = Node::new(id(2)).into_ref();
		let c = Node::new(id(3)).into_ref();

		Node::set_parent_of(&a, &b);
		Node::set_parent_of(&b, &c);
		Node::set_parent_of(&c, &a);

		Node::root(&a);
	}
}
