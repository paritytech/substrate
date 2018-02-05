// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Digest type.

use runtime_std::prelude::*;

#[derive(Clone, Default, PartialEq)]
#[cfg_attr(feature = "with-std", derive(Debug))]
/// The digest of a block, useful for light-clients.
pub struct Digest {
	/// All logs that have happened in the block.
	pub logs: Vec<Vec<u8>>,
}
