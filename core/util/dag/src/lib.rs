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

use std::fmt;
use parity_codec_derive::{Decode, Encode};

#[derive(Clone, Debug, PartialEq)]
pub enum Error<E> {
	Duplicate,
	UnfinalizedRoot,
	Revert,
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
			Error::Duplicate => "Hash already exists in DAG",
			Error::UnfinalizedRoot => "Finalized descendent of DAG root without finalizing root first",
			Error::Revert => "Tried to import or finalize hash that is an ancestor of a previously finalized node",
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

#[derive(Clone, Debug, Decode, Encode)]
pub struct Dag<H, N, V> {
	roots: Vec<Node<H, N, V>>,
	best_finalized_number: Option<N>,
}

impl<H, N, V> Dag<H, N, V> where
	H: PartialEq,
	N: Ord,
{
	pub fn empty() -> Dag<H, N, V> {
		Dag {
			roots: Vec::new(),
			best_finalized_number: None,
		}
	}

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

	pub fn roots(&self) -> impl Iterator<Item=(&H, &N)> {
		self.roots.iter().map(|node| (&node.hash, &node.number))
	}

	pub fn finalize_root(&mut self, hash: &H) -> Option<V> {
		if let Some(position) = self.roots.iter().position(|node| node.hash == *hash) {
			let node = self.roots.swap_remove(position);
			self.roots = node.children;
			self.best_finalized_number = Some(node.number);
			return Some(node.data);
		}

		None
	}

	pub fn finalize<F, E>(
		&mut self,
		hash: &H,
		number: N,
		is_descendent_of: &F,
	) -> Result<(), Error<E>>
		where E: fmt::Debug,
			  F: Fn(&H, &H) -> Result<bool, E>
	{
		if let Some(ref best_finalized_number) = self.best_finalized_number {
			if number <= *best_finalized_number {
				return Err(Error::Revert);
			}
		}

		// check if one of the current roots is being finalized
		if let Some(_) = self.finalize_root(hash) {
			return Ok(());
		}

		// make sure we're not finalizing a descendent of any root
		for root in self.roots.iter() {
			if number > root.number && is_descendent_of(&root.hash, hash)? {
				return Err(Error::UnfinalizedRoot);
			}
		}

		// we finalized a block earlier than any existing root (or possibly
		// another fork not part of the dag). make sure to only keep roots that
		// are part of the finalized branch
		self.roots.retain(|root| {
			root.number > number && is_descendent_of(hash, &root.hash).unwrap_or(false)
		});

		self.best_finalized_number = Some(number);

		Ok(())
	}
}

#[derive(Clone, Debug, Decode, Encode)]
#[cfg_attr(test, derive(PartialEq))]
struct Node<H, N, V> {
	hash: H,
	number: N,
	data: V,
	children: Vec<Node<H, N, V>>,
}

impl<H: PartialEq, N: Ord, V> Node<H, N, V> {
	fn import<F, E: std::error::Error>(
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

#[cfg(test)]
mod test {
	use super::{Dag, Error};

	fn test_dag<'a>() -> (Dag<&'a str, u64, ()>, impl Fn(&&str, &&str) -> Result<bool, ()>)  {
		let mut dag = Dag::empty();

		//
		//     - B - C - D - E
		//    /
		//   /   - G
		//  /   /
		// A - F - H - I
		//  \
		//   — J - K
		//
		let is_descendent_of = |base: &&str, block: &&str| -> Result<bool, ()> {
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

		dag.import("A", 1, (), &is_descendent_of).unwrap();

		dag.import("B", 2, (), &is_descendent_of).unwrap();
		dag.import("C", 3, (), &is_descendent_of).unwrap();
		dag.import("D", 4, (), &is_descendent_of).unwrap();
		dag.import("E", 5, (), &is_descendent_of).unwrap();

		dag.import("F", 2, (), &is_descendent_of).unwrap();
		dag.import("G", 3, (), &is_descendent_of).unwrap();

		dag.import("H", 3, (), &is_descendent_of).unwrap();
		dag.import("I", 4, (), &is_descendent_of).unwrap();

		dag.import("J", 2, (), &is_descendent_of).unwrap();
		dag.import("K", 3, (), &is_descendent_of).unwrap();

		(dag, is_descendent_of)
	}

	#[test]
	fn import_doesnt_revert() {
		let (mut dag, is_descendent_of) = test_dag();

		dag.finalize_root(&"A");

		assert_eq!(
			dag.best_finalized_number,
			Some(1),
		);

		assert_eq!(
			dag.import("A", 1, (), &is_descendent_of),
			Err(Error::Revert),
		);
	}

	#[test]
	fn import_doesnt_add_duplicates() {
		let (mut dag, is_descendent_of) = test_dag();

		assert_eq!(
			dag.import("A", 1, (), &is_descendent_of),
			Err(Error::Duplicate),
		);

		assert_eq!(
			dag.import("I", 4, (), &is_descendent_of),
			Err(Error::Duplicate),
		);

		assert_eq!(
			dag.import("G", 3, (), &is_descendent_of),
			Err(Error::Duplicate),
		);

		assert_eq!(
			dag.import("K", 3, (), &is_descendent_of),
			Err(Error::Duplicate),
		);
	}

	#[test]
	fn finalize_root_works() {
		let finalize_a = || {
			let (mut dag, ..) = test_dag();

			assert_eq!(
				dag.roots().map(|(h, n)| (h.clone(), n.clone())).collect::<Vec<_>>(),
				vec![("A", 1)],
			);

			// finalizing "A" opens up three possible forks
			dag.finalize_root(&"A");

			assert_eq!(
				dag.roots().map(|(h, n)| (h.clone(), n.clone())).collect::<Vec<_>>(),
				vec![("B", 2), ("F", 2), ("J", 2)],
			);

			dag
		};

		{
			let mut dag = finalize_a();

			// finalizing "B" will progress on its fork and remove any other competing forks
			dag.finalize_root(&"B");

			assert_eq!(
				dag.roots().map(|(h, n)| (h.clone(), n.clone())).collect::<Vec<_>>(),
				vec![("C", 3)],
			);

			// all the other forks have been pruned
			assert!(dag.roots.len() == 1);
		}

		{
			let mut dag = finalize_a();

			// finalizing "J" will progress on its fork and remove any other competing forks
			dag.finalize_root(&"J");

			assert_eq!(
				dag.roots().map(|(h, n)| (h.clone(), n.clone())).collect::<Vec<_>>(),
				vec![("K", 3)],
			);

			// all the other forks have been pruned
			assert!(dag.roots.len() == 1);
		}
	}

	#[test]
	fn finalize_works() {
		let (mut dag, is_descendent_of) = test_dag();

		let original_roots = dag.roots.clone();

		// finalizing a block prior to any in the node doesn't change the dag
		dag.finalize(&"0", 0, &is_descendent_of).unwrap();
		assert_eq!(dag.roots, original_roots);

		// finalizing "A" opens up three possible forks
		dag.finalize(&"A", 1, &is_descendent_of).unwrap();
		assert_eq!(
			dag.roots().map(|(h, n)| (h.clone(), n.clone())).collect::<Vec<_>>(),
			vec![("B", 2), ("F", 2), ("J", 2)],
		);

		// finalizing anything lower than what we observed will fail
		assert_eq!(
			dag.best_finalized_number,
			Some(1),
		);

		assert_eq!(
			dag.finalize(&"Z", 1, &is_descendent_of),
			Err(Error::Revert),
		);

		// trying to finalize a node without finalizing its ancestors first will fail
		assert_eq!(
			dag.finalize(&"H", 3, &is_descendent_of),
			Err(Error::UnfinalizedRoot),
		);

		// after finalizing "F" we can finalize "H"
		dag.finalize(&"F", 2, &is_descendent_of).unwrap();
		dag.finalize(&"H", 3, &is_descendent_of).unwrap();

		assert_eq!(
			dag.roots().map(|(h, n)| (h.clone(), n.clone())).collect::<Vec<_>>(),
			vec![("I", 4)],
		);

		// finalizing a node from another fork that isn't part of the dag clears the dag
		dag.finalize(&"Z", 5, &is_descendent_of).unwrap();
		assert!(dag.roots.is_empty());
	}
}
