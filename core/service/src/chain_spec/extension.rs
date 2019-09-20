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

/// A `ChainSpec` extension.
pub trait Extension: Sized {
	/// An associated type containing fork definition.
	type Fork: Fork<Base=Self>;

	/// Convert to fork type.
	fn to_fork(self) -> Self::Fork;
}

/// A `ChainSpec` extension fork definition.
///
/// Basically should look the same as `Extension`, but
/// all parameters are optional. This allows changing
/// only one parameter as part of the fork.
/// The forks can be combined (summed up) to specify
/// a complete set of parameters
pub trait Fork: Sized {
	/// A base `Extension` type.
	type Base: Extension<Fork=Self>;

	/// Combine with another struct.
	///
	/// All parameters set in `other` should override the
	/// ones in the current struct.
	fn combine_with(&mut self, other: Self);

	/// Attempt to convert to the base type if all parameters are set.
	fn to_base(self) -> Result<Self::Base, Self>;
}

macro_rules! impl_trivial {
	() => {};
	($A : ty) => {
		impl_trivial!($A ,);
	};
	($A : ty , $( $B : ty ),*) => {
		impl_trivial!($( $B ),*);

		impl Extension for $A {
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

			fn to_base(self) -> Result<Self::Base, Self> {
				Ok(self)
			}
		}
	}
}

impl_trivial!(u8, u16, u32, u64, usize, String, Vec<u8>);

impl<T: Extension> Extension for Option<T> {
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

	fn to_base(self) -> Result<Self::Base, Self> {
		// TODO [ToDr] Handle error
		Ok(self.map(|x| x.to_base().ok().unwrap()))
	}
}

/// A collection of `ChainSpec` extensions.
pub trait Extensions {
	/// Get an extension of specific type.
	fn get<T: Extension + 'static>(&self) -> Option<&T>;
}

#[derive(Debug, serde::Serialize, serde::Deserialize)]
pub struct Forks<BlockNumber: Ord, T: Extension> where
	T::Fork: serde::Serialize + serde::de::DeserializeOwned,
{
	#[serde(flatten)]
	base: T,
	forks: BTreeMap<BlockNumber, T::Fork>,
}

impl<B: Ord, T: Extension + Clone> Forks<B, T> where
	T::Fork: serde::Serialize + serde::de::DeserializeOwned + Clone + Debug,
{
	/// Create new fork definition given the base and the forks.
	pub fn new(base: T, forks: BTreeMap<B, T::Fork>) -> Self {
		Self { base, forks }
	}

	/// Return a set of parameters for `Extension` including all forks up to `block` (inclusive).
	pub fn for_block(&self, block: B) -> T {
		let mut start = self.base.clone().to_fork();

		println!("Starting: {:?}", start);
		for (_, fork) in self.forks.range(..=block) {
			start.combine_with(fork.clone());
			println!("Combined: {:?} + {:?}", start, fork);
		}

		start
			.to_base()
			.expect("We start from the `base` object, so it's always fully initialized; qed")
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use serde::{Serialize, Deserialize};

	#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
	pub struct Extension1 {
		pub test: u64,
	}

	impl Extension for Extension1 {
		type Fork = Extension1Fork;

		fn to_fork(self) -> Self::Fork {
			Extension1Fork {
				test: Some(self.test.to_fork()),
			}
		}
	}

	#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
	pub struct Extension1Fork {
		pub test: Option<u64>,
	}

	impl Fork for Extension1Fork {
		type Base = Extension1;

		fn combine_with(&mut self, other: Self) {
			self.test.combine_with(other.test);
		}

		fn to_base(self) -> Result<Self::Base, Self> {
			if self.test.is_none() {
				Err(self)
			} else {
				Ok(Extension1 {
					test: self.test.unwrap(),
				})
			}
		}
	}

	#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
	pub struct Extension2 {
		pub test: u8,
	}

	impl Extension for Extension2 {
		type Fork = Extension2Fork;

		fn to_fork(self) -> Self::Fork {
			Extension2Fork {
				test: Some(self.test.to_fork()),
			}
		}
	}

	#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
	pub struct Extension2Fork {
		pub test: Option<u8>,
	}

	impl Fork for Extension2Fork {
		type Base = Extension2;

		fn combine_with(&mut self, other: Self) {
			self.test.combine_with(other.test)
		}

		fn to_base(self) -> Result<Self::Base, Self> {
			if self.test.is_none() {
				Err(self)
			} else {
				Ok(Extension2 {
					test: self.test.unwrap().to_base().unwrap(),
				})
			}
		}
	}

	#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
	pub struct Extensions {
		pub ext1: Extension1,
		pub ext2: Extension2,
	}

	impl super::Extensions for Extensions {
		fn get<T: Extension + 'static>(&self) -> Option<&T> {
			use std::any::{Any, TypeId};

			match TypeId::of::<T>() {
				x if x == TypeId::of::<Extension1>() => Any::downcast_ref(&self.ext1),
				x if x == TypeId::of::<Extension2>() => Any::downcast_ref(&self.ext2),
				_ => None,
			}
		}
	}

	impl Extension for Extensions {
		type Fork = ExtensionsFork;

		fn to_fork(self) -> Self::Fork {
			ExtensionsFork {
				ext1: Some(self.ext1.to_fork()),
				ext2: Some(self.ext2.to_fork()),
			}
		}
	}

	#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
	pub struct ExtensionsFork {
		pub ext1: Option<Extension1Fork>,
		pub ext2: Option<Extension2Fork>,
	}

	impl Fork for ExtensionsFork {
		type Base = Extensions;

		fn combine_with(&mut self, other: Self) {
			self.ext1.combine_with(other.ext1);
			self.ext2.combine_with(other.ext2);
		}

		fn to_base(self) -> Result<Self::Base, Self> {
			if self.ext1.is_none() || self.ext2.is_none() {
				Err(self)
			} else {
				Ok(Extensions {
					ext1: self.ext1.unwrap().to_base().unwrap(),
					ext2: self.ext2.unwrap().to_base().unwrap(),
				})
			}
		}
	}

	#[test]
	fn forks_should_work_correctly() {
		use super::Extensions as _ ;

		let forks: Forks<u64, Extensions> = serde_json::from_str(r#"
{
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
		assert_eq!(forks.for_block(0), Extensions {
			ext1: Extension1 { test: 15 },
			ext2: Extension2 { test: 123 },
		});
		assert_eq!(forks.for_block(1), Extensions {
			ext1: Extension1 { test: 5 },
			ext2: Extension2 { test: 123 },
		});
		assert_eq!(forks.for_block(2), Extensions {
			ext1: Extension1 { test: 5 },
			ext2: Extension2 { test: 5 },
		});
		assert_eq!(forks.for_block(4), Extensions {
			ext1: Extension1 { test: 5 },
			ext2: Extension2 { test: 5 },
		});
		assert_eq!(forks.for_block(5), Extensions {
			ext1: Extension1 { test: 5 },
			ext2: Extension2 { test: 1 },
		});
		assert_eq!(forks.for_block(10), Extensions {
			ext1: Extension1 { test: 5 },
			ext2: Extension2 { test: 1 },
		});

		assert!(forks.for_block(10).get::<Extension2>().is_some());
	}


	// #[derive(ChainSpecExtension)]
	// pub struct Extension1 {
	// 	pub test: u64,
	// }
    //
	// #[derive(ChainSpecExtension)]
	// pub struct Extension2 {
	// 	pub test: u8,
	// }
    //
	// extensions! {
	// 	ext1: Extension1,
	// 	ext2: Extension2,
	// }
}
