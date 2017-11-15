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

//! Validator primitives.

use parachain::EgressPosts;

/// Validity result of particular witness and ingress queue.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag="type", content="data")]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub enum WitnessValidity {
	/// The witness is invalid.
	Invalid,
	/// The witness is processed and new egress queue is created.
	/// Also includes current ingress queue delta.
	Valid(EgressPosts),
}

impl WitnessValidity {
	/// The witness is valid.
	pub fn is_valid(&self) -> bool {
		match *self {
			WitnessValidity::Invalid => false,
			WitnessValidity::Valid(..) => true,
		}
	}
}

impl From<Option<EgressPosts>> for WitnessValidity {
	fn from(posts: Option<EgressPosts>) -> Self {
		match posts {
			Some(posts) => WitnessValidity::Valid(posts),
			None => WitnessValidity::Invalid,
		}
	}
}

// TODO [ToDr] This shouldn't be here!
/// Validator logic.
pub trait Validator {
	/// Validation error.
	type Error: ::std::error::Error;

	/// Validates if the provided witness holds given a current ingress queue.
	///
	/// In case of success produces egress posts.
	fn validate(
		&self,
		witness: &::parachain::Witness,
		code: &[u8],
	) -> Result<WitnessValidity, Self::Error>;
}

#[cfg(test)]
mod tests {
	use super::*;
	use parachain::{EgressPosts, Message};
	use polkadot_serializer as ser;

	#[test]
	fn test_witness_validity_serialization() {
		assert_eq!(
			ser::to_string_pretty(&WitnessValidity::Invalid),
			r#"{
  "type": "invalid"
}"#);

		let mut egress = ::std::collections::BTreeMap::new();
		egress.insert(5.into(), vec![Message(vec![1, 2, 3])]);
		egress.insert(7.into(), vec![Message(vec![4, 5, 6])]);
		assert_eq!(
			ser::to_string_pretty(&WitnessValidity::Valid(EgressPosts(egress))),
			r#"{
  "type": "valid",
  "data": {
    "5": [
      "0x010203"
    ],
    "7": [
      "0x040506"
    ]
  }
}"#);
	}
}
