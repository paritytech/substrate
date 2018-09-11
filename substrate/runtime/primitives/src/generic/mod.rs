// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Generic implementations of Extrinsic/Header/Block.

mod unchecked_extrinsic;
mod checked_extrinsic;
mod header;
mod block;
mod digest;
#[cfg(test)]
mod tests;

pub use self::unchecked_extrinsic::UncheckedExtrinsic;
pub use self::checked_extrinsic::CheckedExtrinsic;
pub use self::header::Header;
pub use self::block::{Block, SignedBlock, BlockId};
pub use self::digest::{Digest, DigestItem, DigestItemRef};
