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

use bytes::{self, Vec};
use parachain;

/// Parachain outgoing message.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EgressPost(#[serde(with="bytes")] pub Vec<u8>);

/// Balance upload.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BalanceUpload(#[serde(with="bytes")] pub Vec<u8>);

/// Balance download.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BalanceDownload(#[serde(with="bytes")] pub Vec<u8>);

/// The result of parachain validation.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct ValidationResult {
	/// New head data that should be included in the relay chain state.
	pub head_data: parachain::HeadData,
	/// Outgoing messages (a vec for each parachain).
	pub egress_queues: Vec<Vec<EgressPost>>,
	/// Balance uploads
	pub balance_uploads: Vec<BalanceUpload>,
}

#[cfg(test)]
mod tests {
	use super::*;
	use polkadot_serializer as ser;

	#[test]
	fn test_validation_result() {
		assert_eq!(ser::to_string_pretty(&ValidationResult {
	head_data: parachain::HeadData(vec![1]),
	egress_queues: vec![vec![EgressPost(vec![1])]],
	balance_uploads: vec![BalanceUpload(vec![2])],
			}), r#"{
  "headData": "0x01",
  "egressQueues": [
    [
      "0x01"
    ]
  ],
  "balanceUploads": [
    "0x02"
  ]
}"#);
	}
}
