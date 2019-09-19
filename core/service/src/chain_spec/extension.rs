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

use std::collections::BTreeMap;

/// A `ChainSpec` extension.
trait Extension: Clone {
	/// An associated type containing fork definition.
	type Fork: Fork + From<Self>;
}

/// A `ChainSpec` extension fork definition.
///
/// Basically should look the same as `Extension`, but
/// all parameters are optional. This allows changing
/// only one parameter as part of the fork.
/// The forks can be combined (summed up) to specify
/// a complete set of parameters
trait Fork: Clone {
	/// A base `Extension` type.
	type Base: Extension<Fork=Self>;

	/// Combine with another struct.
	///
	/// All parameters set in `other` should override the
	/// ones in the current struct.
	fn combine_with(&mut self, other: &Self);

	/// Attempt to convert to the base type if all parameters are set.
	fn to_base(self) -> Result<Self::Base, Self>;
}

/// A collection of `ChainSpec` extensions.
pub trait Extensions {
	/// Get an extension of specific type.
	fn get<T: Extension>(&self) -> Option<&T>;
}


pub struct Forks<BlockNumber: Ord, T: Extension> {
	base: T,
	forks: BTreeMap<BlockNumber, T::Fork>,
}

impl<B, T: Extension> Forks<B, T> {
	/// Return a set of parameters for `Extension` including all forks up to `block` (inclusive).
	pub fn for_block(&self, block: BlockNumber) -> T {
		let start = self.base.clone().into();

		for fork in self.forks.range(..=block) {
			start.combine_with(fork);
		}

		start
			.to_base()
			.expect("We start from the `base` object, so it's always fully initialized; qed")
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[derive(ChainSpecExtension)]
	pub struct Extension1 {
		pub test: u64,
	}

	#[derive(ChainSpecExtension)]
	pub struct Extension2 {
		pub test: u8,
	}

	extensions! {
		ext1: Extension1,
		ext2: Extension2,
	}
}
