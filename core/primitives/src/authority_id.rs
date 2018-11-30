// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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


#[cfg(feature = "std")]
use serde::{Serialize, Serializer, Deserialize, Deserializer};
use H256;

/// An identifier for an authority in the consensus algorithm. The same size as ed25519::Public.
#[derive(Clone, Copy, PartialEq, Eq, Default, Encode, Decode)]
pub struct AuthorityId(pub [u8; 32]);

#[cfg(feature = "std")]
impl ::std::fmt::Display for AuthorityId {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		write!(f, "{}", ::ed25519::Public(self.0).to_ss58check())
	}
}

#[cfg(feature = "std")]
impl ::std::fmt::Debug for AuthorityId {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		let h = format!("{}", ::hexdisplay::HexDisplay::from(&self.0));
		write!(f, "{} ({}…{})", ::ed25519::Public(self.0).to_ss58check(), &h[0..8], &h[60..])
	}
}

#[cfg(feature = "std")]
impl ::std::hash::Hash for AuthorityId {
	fn hash<H: ::std::hash::Hasher>(&self, state: &mut H) {
		self.0.hash(state);
	}
}

impl AsRef<[u8; 32]> for AuthorityId {
	fn as_ref(&self) -> &[u8; 32] {
		&self.0
	}
}

impl AsRef<[u8]> for AuthorityId {
	fn as_ref(&self) -> &[u8] {
		&self.0[..]
	}
}

impl Into<[u8; 32]> for AuthorityId {
	fn into(self) -> [u8; 32] {
		self.0
	}
}

impl From<[u8; 32]> for AuthorityId {
	fn from(a: [u8; 32]) -> Self {
		AuthorityId(a)
	}
}

impl AsRef<AuthorityId> for AuthorityId {
	fn as_ref(&self) -> &AuthorityId {
		&self
	}
}

impl Into<H256> for AuthorityId {
	fn into(self) -> H256 {
		self.0.into()
	}
}

#[cfg(feature = "std")]
impl Serialize for AuthorityId {
	fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error> where S: Serializer {
		::ed25519::serialize(&self, serializer)
	}
}

#[cfg(feature = "std")]
impl<'de> Deserialize<'de> for AuthorityId {
	fn deserialize<D>(deserializer: D) -> Result<Self, D::Error> where D: Deserializer<'de> {
		::ed25519::deserialize(deserializer)
	}
}
