use sp_std::{cell::RefCell, rc::Rc, prelude::*};
use sp_runtime::RuntimeDebug;

#[derive(PartialEq, Eq, Clone, RuntimeDebug)]
pub(crate) enum NodeRole {
	Voter,
	Target,
}

pub(crate) type RefCellOf<T> = Rc<RefCell<T>>;
pub(crate) type NodeRef<A> = RefCellOf<Node<A>>;

#[derive(Clone)]
pub(crate) struct Node<A> {
	/// Assumed to be unique.
	pub(crate) who: A,
	pub(crate) role: NodeRole,
	pub(crate) parent: Option<NodeRef<A>>,
}

impl<A: PartialEq> PartialEq for Node<A> {
	fn eq(&self, other: &Node<A>) -> bool {
		self.who == other.who
	}
}

impl<A: PartialEq> Eq for Node<A> {}

#[cfg(feature = "std")]
impl<A: sp_std::fmt::Debug + Clone> sp_std::fmt::Debug for Node<A> {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		write!(f, "({:?} --> {:?})", self.who, self.parent.as_ref().map(|p| p.borrow().who.clone()))
	}
}

impl<A: PartialEq + Eq + Clone + sp_std::fmt::Debug> Node<A> {
	pub fn new(who: A, role: NodeRole) -> Node<A> {
		Self {
			who,
			role,
			parent: None,
		}
	}

	pub fn has_parent(&self) -> bool {
		self.parent.is_some()
	}

	pub fn is_parent_of(who: &NodeRef<A>, other: &NodeRef<A>) -> bool {
		if who.borrow().parent.is_none() {
			return false;
		}
		who.borrow().parent.as_ref() == Some(other)
	}

	pub fn remove_parent(who: &NodeRef<A>) {
		who.borrow_mut().parent = None;
	}

	pub fn set_parent_of(target: &NodeRef<A>, parent: &NodeRef<A>) {
		target.borrow_mut().parent = Some(parent.clone());
	}

	pub fn root(start: &NodeRef<A>) -> (NodeRef<A>, Vec<NodeRef<A>>) {
		let mut parent_path: Vec<NodeRef<A>> = Vec::new();
		let initial = start.clone();
		parent_path.push(start.clone());
		let mut current = start.clone();

		while let Some(ref next_parent) = current.clone().borrow().parent {
			if initial == next_parent.clone() { break; }
			parent_path.push(next_parent.clone());
			current = next_parent.clone();
		}

		(current, parent_path)
	}

	pub fn parent(&self) -> Option<A> {
		self.parent.as_ref().map(|r| r.borrow().who.clone())
	}

	pub fn into_ref(self) -> NodeRef<A> {
		Rc::from(RefCell::from(self))
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn basic_create_works() {
		let node = Node::new(10u32, NodeRole::Target);
		assert_eq!(node, Node { who: 10u32, parent: None, role: NodeRole::Target });
	}

	#[test]
	fn set_parent_works() {
		let a = Node::new(10u32, NodeRole::Target).into_ref();
		let b = Node::new(20u32, NodeRole::Target).into_ref();

		assert_eq!(a.borrow().parent, None);
		Node::set_parent_of(&a, &b);
		assert_eq!(*a.borrow().parent.as_ref().unwrap(), b);
	}

	#[test]
	fn get_root_singular() {
		let a = Node::new(1u32, NodeRole::Target).into_ref();
		assert_eq!(Node::root(&a), (a.clone(), vec![a.clone()]));
	}

	#[test]
	fn get_root_works() {
		//	D <-- A <-- B <-- C
		//			\
		//			 <-- E
		let a = Node::new(1u32, NodeRole::Target).into_ref();
		let b = Node::new(2u32, NodeRole::Target).into_ref();
		let c = Node::new(3u32, NodeRole::Target).into_ref();
		let d = Node::new(4u32, NodeRole::Target).into_ref();
		let e = Node::new(5u32, NodeRole::Target).into_ref();
		let f = Node::new(6u32, NodeRole::Target).into_ref();

		Node::set_parent_of(&c, &b);
		Node::set_parent_of(&b, &a);
		Node::set_parent_of(&e, &a);
		Node::set_parent_of(&a, &d);

		assert_eq!(
			Node::root(&e),
			(d.clone(), vec![e.clone(), a.clone(), d.clone()]),
		);

		assert_eq!(
			Node::root(&a),
			(d.clone(), vec![a.clone(), d.clone()]),
		);

		assert_eq!(
			Node::root(&c),
			(d.clone(), vec![c.clone(), b.clone(), a.clone(), d.clone()]),
		);

		//	D 	    A <-- B <-- C
		//	F <-- /	\
		//			 <-- E
		Node::set_parent_of(&a, &f);

		assert_eq!(
			Node::root(&a),
			(f.clone(), vec![a.clone(), f.clone()]),
		);

		assert_eq!(
			Node::root(&c),
			(f.clone(), vec![c.clone(), b.clone(), a.clone(), f.clone()]),
		);
	}

	#[test]
	fn get_root_on_cycle() {
		// A ---> B
		// |      |
		//  <---- C
		let a = Node::new(1u32, NodeRole::Target).into_ref();
		let b = Node::new(2u32, NodeRole::Target).into_ref();
		let c = Node::new(3u32, NodeRole::Target).into_ref();

		Node::set_parent_of(&a, &b);
		Node::set_parent_of(&b, &c);
		Node::set_parent_of(&c, &a);

		let (root, path) = Node::root(&a);
		assert_eq!(root, c);
		assert_eq!(path.clone(), vec![a.clone(), b.clone(), c.clone()]);
	}

	#[test]
	fn node_cmp_stack_overflows_on_non_unique_elements() {
		// To make sure we don't stack overflow on duplicate who. This needs manual impl of
		// PartialEq.
		let a = Node::new(1u32, NodeRole::Target).into_ref();
		let b = Node::new(1u32, NodeRole::Target).into_ref();
		let c = Node::new(1u32, NodeRole::Target).into_ref();

		Node::set_parent_of(&a, &b);
		Node::set_parent_of(&b, &c);
		Node::set_parent_of(&c, &a);

		Node::root(&a);
	}
}
