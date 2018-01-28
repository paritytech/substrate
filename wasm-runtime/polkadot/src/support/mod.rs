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

//! Support code for the runtime.

mod environment;
pub mod storage;
mod hashable;
#[cfg(feature = "with-std")]
mod statichex;
#[macro_use]
#[cfg(feature = "with-std")]
mod testing;

pub use self::environment::with_env;
pub use self::storage::StorageVec;
pub use self::hashable::Hashable;
#[cfg(feature = "with-std")]
pub use self::statichex::{StaticHexConversion, StaticHexInto};
#[cfg(feature = "with-std")]
pub use self::testing::{AsBytesRef, HexDisplay, TestExternalities, one, two};
