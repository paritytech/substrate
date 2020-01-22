use sp_std::{cell::RefCell, rc::Rc, prelude::*};
use sp_runtime::RuntimeDebug;

#[derive(PartialEq, Eq, Ord, PartialOrd, Clone, RuntimeDebug)]
pub(crate) enum NodeRole {
	Voter,
	Target,
}

pub(crate) type RefCellOf<T> = Rc<RefCell<T>>;
pub(crate) type NodeRef<A> = RefCellOf<Node<A>>;

#[derive(PartialOrd, Ord, Clone)]
pub(crate) struct NodeId<A> {
	/// Assumed to be unique.
	pub who: A,
	pub role: NodeRole,
}

impl<A> NodeId<A> {
	pub fn from(who: A, role: NodeRole) -> Self {
		Self { who, role }
	}
}

impl<A: PartialEq> PartialEq for NodeId<A> {
	fn eq(&self, other: &NodeId<A>) -> bool {
		self.who == other.who && self.role == other.role
	}
}

#[cfg(feature = "std")]
impl<A: sp_std::fmt::Debug + Clone> sp_std::fmt::Debug for NodeId<A> {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		write!(f, "Node({:?}, {:?})", self.who, if self.role == NodeRole::Voter { "V" } else { "T" })
	}
}

impl<A: PartialEq> Eq for NodeId<A> {}

#[derive(Clone)]
pub(crate) struct Node<A> {
	pub(crate) id: NodeId<A>,
	pub(crate) parent: Option<NodeRef<A>>,
}

impl<A: PartialEq> PartialEq for Node<A> {
	fn eq(&self, other: &Node<A>) -> bool {
		self.id == other.id
	}
}

impl<A: PartialEq> Eq for Node<A> {}

#[cfg(feature = "std")]
impl<A: sp_std::fmt::Debug + Clone> sp_std::fmt::Debug for Node<A> {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter<'_>) -> sp_std::fmt::Result {
		write!(f, "({:?} --> {:?})", self.id, self.parent.as_ref().map(|p| p.borrow().id.clone()))
	}
}

impl<A: PartialEq + Eq + Clone + sp_std::fmt::Debug> Node<A> {
	pub fn new(id: NodeId<A>) -> Node<A> {
		Self { id, parent: None }
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
		//	D <-- A <-- B <-- C
		//			\
		//			 <-- E
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
