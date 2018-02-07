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

#[cfg(feature = "std")]
use primitives::bytes;
use rstd::vec::Vec;
use parachain;

/// Parachain outgoing message.
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct EgressPost(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Balance upload.
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct BalanceUpload(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Balance download.
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
pub struct BalanceDownload(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// The result of parachain validation.
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
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
	use substrate_serializer as ser;

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
