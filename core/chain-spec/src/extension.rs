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

//! Chain Spec extensions helpers.

use std::fmt::Debug;
use std::collections::BTreeMap;

use serde::{Serialize, Deserialize, de::DeserializeOwned};

/// A `ChainSpec` extension.
pub trait Group: Sized {
	/// An associated type containing fork definition.
	type Fork: Fork<Base=Self>;

	/// Convert to fork type.
	fn to_fork(self) -> Self::Fork;
}

/// A `ChainSpec` extension fork definition.
///
/// Basically should look the same as `Group`, but
/// all parameters are optional. This allows changing
/// only one parameter as part of the fork.
/// The forks can be combined (summed up) to specify
/// a complete set of parameters
pub trait Fork: Sized {
	/// A base `Group` type.
	type Base: Group<Fork=Self>;

	/// Combine with another struct.
	///
	/// All parameters set in `other` should override the
	/// ones in the current struct.
	fn combine_with(&mut self, other: Self);

	/// Attempt to convert to the base type if all parameters are set.
	fn to_base(self) -> Option<Self::Base>;
}

macro_rules! impl_trivial {
	() => {};
	($A : ty) => {
		impl_trivial!($A ,);
	};
	($A : ty , $( $B : ty ),*) => {
		impl_trivial!($( $B ),*);

		impl Group for $A {
			type Fork = $A;

			fn to_fork(self) -> Self::Fork {
				self
			}
		}

		impl Fork for $A {
			type Base = $A;

			fn combine_with(&mut self, other: Self) {
				*self = other;
			}

			fn to_base(self) -> Option<Self::Base> {
				Some(self)
			}
		}
	}
}

impl_trivial!((), u8, u16, u32, u64, usize, String, Vec<u8>);

impl<T: Group> Group for Option<T> {
	type Fork = Option<T::Fork>;

	fn to_fork(self) -> Self::Fork {
		self.map(|a| a.to_fork())
	}
}

impl<T: Fork> Fork for Option<T> {
	type Base = Option<T::Base>;

	fn combine_with(&mut self, other: Self) {
		*self = match (self.take(), other) {
			(Some(mut a), Some(b)) => {
				a.combine_with(b);
				Some(a)
			},
			(a, b) => a.or(b),
		};
	}

	fn to_base(self) -> Option<Self::Base> {
		self.map(|x| x.to_base())
	}
}

/// A collection of `ChainSpec` extensions.
pub trait Extension: Group + Serialize + DeserializeOwned + Clone {
	/// Get an extension of specific type.
	fn get<T: Group + 'static>(&self) -> Option<&T>;
}

impl Extension for () {
	fn get<T: Group + 'static>(&self) -> Option<&T> { None }
}

impl Extension for Option<()> {
	fn get<T: Group + 'static>(&self) -> Option<&T> { None }
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Forks<BlockNumber: Ord, T: Group> where
	T::Fork: Serialize + DeserializeOwned,
{
	#[serde(flatten)]
	base: T,
	forks: BTreeMap<BlockNumber, T::Fork>,
}

impl<B: Ord, T: Group + Default> Default for Forks<B, T> where
	T::Fork: Serialize + DeserializeOwned,
{
	fn default() -> Self {
		Self {
			base: Default::default(),
			forks: Default::default(),
		}
	}
}

impl<B: Ord, T: Group + Clone> Forks<B, T> where
	T::Fork: Serialize + DeserializeOwned + Clone + Debug,
{
	/// Create new fork definition given the base and the forks.
	pub fn new(base: T, forks: BTreeMap<B, T::Fork>) -> Self {
		Self { base, forks }
	}

	/// Return a set of parameters for `Group` including all forks up to `block` (inclusive).
	pub fn at_block(&self, block: B) -> T {
		let mut start = self.base.clone().to_fork();

		for (_, fork) in self.forks.range(..=block) {
			start.combine_with(fork.clone());
		}

		start
			.to_base()
			.expect("We start from the `base` object, so it's always fully initialized; qed")
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use chain_spec_derive::{ChainSpecGroup, ChainSpecExtension};

	#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, ChainSpecGroup)]
	pub struct Extension1 {
		pub test: u64,
	}

	#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, ChainSpecGroup)]
	pub struct Extension2 {
		pub test: u8,
	}

	#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, ChainSpecExtension)]
	pub struct Extensions {
		pub ext1: Extension1,
		pub ext2: Extension2,
	}

	#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, ChainSpecExtension)]
	pub struct Ext2 {
		pub non_fork: Extension1,
		#[serde(flatten)]
		pub forks: Forks<u64, Extensions>,
	}

	// impl super::Extension for Extensions {
	// 	fn get<T: Extension + 'static>(&self) -> Option<&T> {
	// 		use std::any::{Any, TypeId};
    //
	// 		match TypeId::of::<T>() {
	// 			x if x == TypeId::of::<Extension1>() => Any::downcast_ref(&self.ext1),
	// 			x if x == TypeId::of::<Extension2>() => Any::downcast_ref(&self.ext2),
	// 			_ => None,
	// 		}
	// 	}
	// }

	#[test]
	fn forks_should_work_correctly() {
		use super::Extension as _ ;

		let ext: Ext2 = serde_json::from_str(r#"
{
	"non_fork": {
		"test": 11
	},
	"ext1": {
		"test": 15
	},
	"ext2": {
		"test": 123
	},
	"forks": {
		"1": {
			"ext1": { "test": 5 }
		},
		"2": {
			"ext2": { "test": 5 }
		},
		"5": {
			"ext2": { "test": 1 }
		}
	}
}
		"#).unwrap();

		assert_eq!(ext.get::<Extension1>(), Extension1 {
			test: 11
		});

		// get forks definition
		let forks = ext.get::<Forks<u64, Extensions>>().unwrap();
		assert_eq!(forks.at_block(0), Extensions {
			ext1: Extension1 { test: 15 },
			ext2: Extension2 { test: 123 },
		});
		assert_eq!(forks.at_block(1), Extensions {
			ext1: Extension1 { test: 5 },
			ext2: Extension2 { test: 123 },
		});
		assert_eq!(forks.at_block(2), Extensions {
			ext1: Extension1 { test: 5 },
			ext2: Extension2 { test: 5 },
		});
		assert_eq!(forks.at_block(4), Extensions {
			ext1: Extension1 { test: 5 },
			ext2: Extension2 { test: 5 },
		});
		assert_eq!(forks.at_block(5), Extensions {
			ext1: Extension1 { test: 5 },
			ext2: Extension2 { test: 1 },
		});
		assert_eq!(forks.at_block(10), Extensions {
			ext1: Extension1 { test: 5 },
			ext2: Extension2 { test: 1 },
		});

		assert!(forks.at_block(10).get::<Extension2>().is_some());
	}
}
