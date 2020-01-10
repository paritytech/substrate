// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Substrate RPC primitives and utilities.

#![warn(missing_docs)]

pub mod number;
pub mod list;

/// A util function to assert the result of serialization and deserialization is the same.
#[cfg(test)]
pub(crate) fn assert_deser<T>(s: &str, expected: T) where
	T: std::fmt::Debug + serde::ser::Serialize + serde::de::DeserializeOwned + PartialEq
{
	assert_eq!(
		serde_json::from_str::<T>(s).unwrap(),
		expected
	);
	assert_eq!(
		serde_json::to_string(&expected).unwrap(),
		s
	);
}

