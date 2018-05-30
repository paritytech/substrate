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

//! Parachain data types.

#[cfg(feature = "std")]
use primitives::bytes;
use primitives;
use codec::{Input, Slicable};
use rstd::cmp::{PartialOrd, Ord, Ordering};
use rstd::vec::Vec;
use ::Hash;

#[cfg(test)]
mod tests {
	use super::*;
	use substrate_serializer as ser;

	#[test]
	fn test_candidate() {
		assert_eq!(ser::to_string_pretty(&Candidate {
			parachain_index: 5.into(),
			collator_signature: primitives::hash::H512::from(10).into(),
			unprocessed_ingress: ConsolidatedIngress(vec![
				(Id(1), vec![Message(vec![2])]),
				(Id(2), vec![Message(vec![2]), Message(vec![3])]),
			]),
			block: BlockData(vec![1, 2, 3]),
    }), r#"{
  "parachainIndex": 5,
  "collatorSignature": "0x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000a",
  "unprocessedIngress": [
    [
      1,
      [
        "0x02"
      ]
    ],
    [
      2,
      [
        "0x02",
        "0x03"
      ]
    ]
  ],
  "block": "0x010203"
}"#);
	}
}
