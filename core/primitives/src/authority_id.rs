// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use parity_codec::{Encode, Decode};
use crate::{H256, H512};

// TODO: Remove the following two identifiers, and replace their usage with ed25519::Public and ::Signature.
// This will require opening the ed25519 module up to no-std, and thus guarding all the algorithmic code
// (key init, sign, verify, ...) with std feature gate.

/// An identifier for an authority in the consensus algorithm. The same size as ed25519::Public.
#[derive(Clone, Copy, PartialEq, Eq, Default, Encode, Decode)]
pub struct Ed25519AuthorityId(pub [u8; 32]);

/// An identifier for an authority's signature in the consensus algorithm. The same size as ed25519::Signature.
#[derive(Clone, Copy, PartialEq, Eq, Default, Encode, Decode, Debug, Hash)]
pub struct Ed25519Signature(pub H512);

