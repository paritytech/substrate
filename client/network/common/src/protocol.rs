// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use std::{
	fmt,
	hash::{Hash, Hasher},
	ops::Deref,
	sync::Arc,
};

pub mod event;

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
