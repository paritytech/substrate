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

#[derive(Clone, PartialEq)]
pub enum Error<E> {
	Duplicate,
	Client(E),
}

impl<E: fmt::Debug> fmt::Debug for Error<E> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Error::Duplicate => write!(f, "Hash already exists in DAG"),
			Error::Client(ref err) => fmt::Debug::fmt(err, f),
		}
	}
}

impl<E: fmt::Debug> From<E> for Error<E> {
	fn from(err: E) -> Error<E> {
		Error::Client(err)
	}
}

#[derive(Debug)]
pub struct Dag<H, N, V> {
	roots: Vec<Node<H, N, V>>,
}

impl<H, N, V> Dag<H, N, V> where
	H: PartialEq,
	N: Ord
{
	pub fn empty() -> Dag<H, N, V> {
		Dag { roots: Vec::new() }
	}

	// FIXME: don't import <= `best_finalized`
	pub fn import<F, E>(
		&mut self,
		mut hash: H,
		mut number: N,
		mut data: V,
		is_descendent_of: &F,
	) -> Result<bool, Error<E>>
		where E: fmt::Debug,
			  F: Fn(&H, &H) -> Result<bool, E>,
	{
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

	pub fn apply(&mut self, hash: &H) -> Option<V> {
		if let Some(position) = self.roots.iter().position(|node| node.hash == *hash) {
			let node = self.roots.swap_remove(position);
			self.roots = node.children;
			return Some(node.data);
		}

		None
	}
}

#[derive(Debug)]
struct Node<H, N, V> {
	hash: H,
	number: N,
	data: V,
	children: Vec<Node<H, N, V>>,
}

impl<H: PartialEq, N: Ord, V> Node<H, N, V> {
	fn import<F, E: fmt::Debug>(
		&mut self,
		mut hash: H,
		mut number: N,
		mut data: V,
		is_descendent_of: &F,
	) -> Result<Option<(H, N, V)>, Error<E>>
		where E: fmt::Debug,
			  F: Fn(&H, &H) -> Result<bool, E>,
	{
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

		if self.hash == hash {
			return Err(Error::Duplicate);
		};

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
	use super::Dag;

	fn test_dag<'a>() -> Dag<&'a str, u64, ()> {
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
				_ => unreachable!(),
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

		dag
	}

	#[test]
	fn it_works() {
		let apply_a = || {
			let mut dag = test_dag();

			assert_eq!(
				dag.roots().map(|(h, n)| (h.clone(), n.clone())).collect::<Vec<_>>(),
				vec![("A", 1)],
			);

			// applying "A" opens up three possible forks
			dag.apply(&"A");

			assert_eq!(
				dag.roots().map(|(h, n)| (h.clone(), n.clone())).collect::<Vec<_>>(),
				vec![("B", 2), ("F", 2), ("J", 2)],
			);

			dag
		};

		{
			let mut dag = apply_a();

			// applying "B" will progress on its fork and remove any other competing forks
			dag.apply(&"B");

			assert_eq!(
				dag.roots().map(|(h, n)| (h.clone(), n.clone())).collect::<Vec<_>>(),
				vec![("C", 3)],
			);

			// all the other forks have been pruned
			assert!(dag.roots.len() == 1);
		}

		{
			let mut dag = apply_a();

			// applying "J" will progress on its fork and remove any other competing forks
			dag.apply(&"J");

			assert_eq!(
				dag.roots().map(|(h, n)| (h.clone(), n.clone())).collect::<Vec<_>>(),
				vec![("K", 3)],
			);

			// all the other forks have been pruned
			assert!(dag.roots.len() == 1);
		}
	}
}
