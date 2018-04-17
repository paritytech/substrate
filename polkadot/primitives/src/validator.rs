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
use codec::Slicable;

/// Parachain outgoing message.
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
pub struct EgressPost(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Balance upload.
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
pub struct BalanceUpload(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Balance download.
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
pub struct BalanceDownload(#[cfg_attr(feature = "std", serde(with="bytes"))] pub Vec<u8>);

/// Validation parameters for evaluating the parachain validity function.
// TODO: consolidated ingress and balance downloads
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct ValidationParams {
	/// The collation body.
	pub block_data: parachain::BlockData,
	/// Previous head-data.
	pub parent_head: parachain::HeadData,
}

impl Slicable for ValidationParams {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		self.block_data.0.using_encoded(|s| v.extend(s));
		self.parent_head.0.using_encoded(|s| v.extend(s));

		v
	}

	fn decode<I: ::codec::Input>(input: &mut I) -> Option<Self> {
		Some(ValidationParams {
			block_data: Slicable::decode(input).map(parachain::BlockData)?,
			parent_head: Slicable::decode(input).map(parachain::HeadData)?,
		})
	}
}

/// The result of parachain validation.
// TODO: egress and balance uploads
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
#[cfg_attr(feature = "std", serde(deny_unknown_fields))]
pub struct ValidationResult {
	/// New head data that should be included in the relay chain state.
	pub head_data: parachain::HeadData,
}

impl Slicable for ValidationResult {
	fn encode(&self) -> Vec<u8> {
		self.head_data.0.encode()
	}

	fn decode<I: ::codec::Input>(input: &mut I) -> Option<Self> {
		Some(ValidationResult {
			head_data: Slicable::decode(input).map(parachain::HeadData)?,
		})
	}
}
