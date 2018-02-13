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

//! State machine backends. These manage the code and storage of contracts.

use std::{error, fmt};
use std::collections::HashMap;

/// A state backend is used to read state data and can have changes committed
/// to it.
pub trait Backend {
	/// An error type when fetching data is not possible.
	type Error: super::Error;

	/// Get keyed storage associated with specific address, or None if there is nothing associated.
	fn storage(&self, key: &[u8]) -> Result<Option<&[u8]>, Self::Error>;

	/// Commit updates to the backend and get new state.
	fn commit<I>(&mut self, changes: I)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>;

	/// Get all key/value pairs into a Vec.
	fn pairs(&self) -> Vec<(&[u8], &[u8])>;
}

/// Error impossible.
// TODO: use `!` type when stabilized.
#[derive(Debug)]
pub enum Void {}

impl fmt::Display for Void {
	fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
		match *self {}
	}
}

impl error::Error for Void {
	fn description(&self) -> &str { "unreachable error" }
}

/// In-memory backend. Fully recomputes tries on each commit but useful for
/// tests.
pub type InMemory = HashMap<Vec<u8>, Vec<u8>>;

impl Backend for InMemory {
	type Error = Void;

	fn storage(&self, key: &[u8]) -> Result<Option<&[u8]>, Self::Error> {
		Ok(self.get(key).map(AsRef::as_ref))
	}

	fn commit<I>(&mut self, changes: I)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		for (key, val) in changes {
			match val {
				Some(v) => { self.insert(key, v); },
				None => { self.remove(&key); },
			}
		}
	}

	fn pairs(&self) -> Vec<(&[u8], &[u8])> {
		self.iter().map(|(k, v)| (&k[..], &v[..])).collect()
	}
}

// TODO: DB-based backend
