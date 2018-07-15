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

//! Hashable trait.

use codec::Codec;
use runtime_io::{blake2_256, twox_128, twox_256};

pub trait Hashable: Sized {
	fn blake2_256(&self) -> [u8; 32];
	fn twox_128(&self) -> [u8; 16];
	fn twox_256(&self) -> [u8; 32];
}

impl<T: Codec> Hashable for T {
	fn blake2_256(&self) -> [u8; 32] {
		blake2_256(&self.encode())
	}
	fn twox_128(&self) -> [u8; 16] {
		twox_128(&self.encode())
	}
	fn twox_256(&self) -> [u8; 32] {
		twox_256(&self.encode())
	}
}
