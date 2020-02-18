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

//! RPC a lenient list or value type.

use serde::{Serialize, Deserialize};

/// RPC list or value wrapper.
///
/// For some RPCs it's convenient to call them with either
/// a single value or a whole list of values to get a proper response.
/// In theory you could do a batch query, but it's:
/// 1. Less convenient in client libraries
/// 2. If the response value is small, the protocol overhead might be dominant.
///
/// Also it's nice to be able to maintain backward compatibility for methods that
/// were initially taking a value and now we want to expand them to take a list.
#[derive(Serialize, Deserialize, Debug, PartialEq)]
#[serde(untagged)]
pub enum ListOrValue<T> {
	/// A list of values of given type.
	List(Vec<T>),
	/// A single value of given type.
	Value(T),
}

impl<T> ListOrValue<T> {
	/// Map every contained value using function `F`.
	///
	/// This allows to easily convert all values in any of the variants.
	pub fn map<F: Fn(T) -> X, X>(self, f: F) -> ListOrValue<X> {
		match self {
			ListOrValue::List(v) => ListOrValue::List(v.into_iter().map(f).collect()),
			ListOrValue::Value(v) => ListOrValue::Value(f(v)),
		}
	}
}

impl<T> From<T> for ListOrValue<T> {
	fn from(n: T) -> Self {
		ListOrValue::Value(n)
	}
}

impl<T> From<Vec<T>> for ListOrValue<T> {
	fn from(n: Vec<T>) -> Self {
		ListOrValue::List(n)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::assert_deser;

	#[test]
	fn should_serialize_and_deserialize() {
		assert_deser(r#"5"#, ListOrValue::Value(5_u64));
		assert_deser(r#""str""#, ListOrValue::Value("str".to_string()));
		assert_deser(r#"[1,2,3]"#, ListOrValue::List(vec![1_u64, 2_u64, 3_u64]));
	}
}
