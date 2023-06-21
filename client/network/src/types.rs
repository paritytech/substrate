// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! `sc-network` type definitions

use std::{
	borrow::Borrow,
	fmt,
	hash::{Hash, Hasher},
	ops::Deref,
	sync::Arc,
};

/// The protocol name transmitted on the wire.
#[derive(Debug, Clone)]
pub enum ProtocolName {
	/// The protocol name as a static string.
	Static(&'static str),
	/// The protocol name as a dynamically allocated string.
	OnHeap(Arc<str>),
}

impl From<&'static str> for ProtocolName {
	fn from(name: &'static str) -> Self {
		Self::Static(name)
	}
}

impl From<Arc<str>> for ProtocolName {
	fn from(name: Arc<str>) -> Self {
		Self::OnHeap(name)
	}
}

impl From<String> for ProtocolName {
	fn from(name: String) -> Self {
		Self::OnHeap(Arc::from(name))
	}
}

impl Deref for ProtocolName {
	type Target = str;

	fn deref(&self) -> &str {
		match self {
			Self::Static(name) => name,
			Self::OnHeap(name) => &name,
		}
	}
}

impl Borrow<str> for ProtocolName {
	fn borrow(&self) -> &str {
		self
	}
}

impl PartialEq for ProtocolName {
	fn eq(&self, other: &Self) -> bool {
		(self as &str) == (other as &str)
	}
}

impl Eq for ProtocolName {}

impl Hash for ProtocolName {
	fn hash<H: Hasher>(&self, state: &mut H) {
		(self as &str).hash(state)
	}
}

impl fmt::Display for ProtocolName {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.write_str(self)
	}
}

impl AsRef<str> for ProtocolName {
	fn as_ref(&self) -> &str {
		self as &str
	}
}

#[cfg(test)]
mod tests {
	use super::ProtocolName;
	use std::{
		borrow::Borrow,
		collections::hash_map::DefaultHasher,
		hash::{Hash, Hasher},
	};

	#[test]
	fn protocol_name_keys_are_equivalent_to_str_keys() {
		const PROTOCOL: &'static str = "/some/protocol/1";
		let static_protocol_name = ProtocolName::from(PROTOCOL);
		let on_heap_protocol_name = ProtocolName::from(String::from(PROTOCOL));

		assert_eq!(<ProtocolName as Borrow<str>>::borrow(&static_protocol_name), PROTOCOL);
		assert_eq!(<ProtocolName as Borrow<str>>::borrow(&on_heap_protocol_name), PROTOCOL);
		assert_eq!(static_protocol_name, on_heap_protocol_name);

		assert_eq!(hash(static_protocol_name), hash(PROTOCOL));
		assert_eq!(hash(on_heap_protocol_name), hash(PROTOCOL));
	}

	#[test]
	fn different_protocol_names_do_not_compare_equal() {
		const PROTOCOL1: &'static str = "/some/protocol/1";
		let static_protocol_name1 = ProtocolName::from(PROTOCOL1);
		let on_heap_protocol_name1 = ProtocolName::from(String::from(PROTOCOL1));

		const PROTOCOL2: &'static str = "/some/protocol/2";
		let static_protocol_name2 = ProtocolName::from(PROTOCOL2);
		let on_heap_protocol_name2 = ProtocolName::from(String::from(PROTOCOL2));

		assert_ne!(<ProtocolName as Borrow<str>>::borrow(&static_protocol_name1), PROTOCOL2);
		assert_ne!(<ProtocolName as Borrow<str>>::borrow(&on_heap_protocol_name1), PROTOCOL2);
		assert_ne!(static_protocol_name1, static_protocol_name2);
		assert_ne!(static_protocol_name1, on_heap_protocol_name2);
		assert_ne!(on_heap_protocol_name1, on_heap_protocol_name2);
	}

	fn hash<T: Hash>(x: T) -> u64 {
		let mut hasher = DefaultHasher::new();
		x.hash(&mut hasher);
		hasher.finish()
	}
}
