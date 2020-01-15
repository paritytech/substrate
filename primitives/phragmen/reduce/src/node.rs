use std::cell::RefCell;
use std::rc::Rc;

#[derive(PartialEq, Eq, std::fmt::Debug)]
pub(crate) enum NodeRole {
	Voter,
	Target,
}

pub(crate) type NodeRef<A> = Rc<RefCell<Node<A>>>;

#[derive(PartialEq, Eq)]
pub(crate) struct Node<A> {
	pub(crate) who: A,
	pub(crate) role: NodeRole,
	pub(crate) parent: Option<NodeRef<A>>,
}

use std::fmt;
impl<A: fmt::Debug + Clone> fmt::Debug for Node<A> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "({:?} [--> {:?})]", self.who, self.parent.as_ref().map(|p| p.borrow().who.clone()))
	}
}

impl<A> Node<A> {
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

	pub fn set_parent_of(target: &NodeRef<A>, parent: &NodeRef<A>) {
		target.borrow_mut().parent = Some(parent.clone());
	}

	pub fn root(start: &NodeRef<A>) -> (NodeRef<A>, Vec<NodeRef<A>>) {
		let mut parent_path: Vec<NodeRef<A>> = Vec::new();
		parent_path.push(start.clone());

		let mut current = parent_path[0].clone();
		while let Some(ref next_parent) = current.clone().borrow().parent {
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
		let d = Node::new(1u32, NodeRole::Target).into_ref();
		let a = Node::new(1u32, NodeRole::Target).into_ref();
		let b = Node::new(1u32, NodeRole::Target).into_ref();
		let c = Node::new(1u32, NodeRole::Target).into_ref();
		let e = Node::new(1u32, NodeRole::Target).into_ref();
		let f = Node::new(1u32, NodeRole::Target).into_ref();

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
			(d.clone(), vec![c.clone(), b.clone(), a.clone(), f.clone()]),
		);
	}
}
