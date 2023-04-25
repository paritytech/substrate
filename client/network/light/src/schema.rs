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

//! Include sources generated from protobuf definitions.

pub(crate) mod v1 {
	pub(crate) mod light {
		include!(concat!(env!("OUT_DIR"), "/api.v1.light.rs"));
	}
}

#[cfg(test)]
mod tests {
	use prost::Message as _;

	#[test]
	fn empty_proof_encodes_correctly() {
		let encoded = super::v1::light::Response {
			response: Some(super::v1::light::response::Response::RemoteReadResponse(
				super::v1::light::RemoteReadResponse { proof: Some(Vec::new()) },
			)),
		}
		.encode_to_vec();

		// Make sure that the response contains one field of number 2 and wire type 2 (message),
		// then another field of number 2 and wire type 2 (bytes), then a length of 0.
		assert_eq!(encoded, vec![(2 << 3) | 2, 2, (2 << 3) | 2, 0]);
	}

	#[test]
	fn no_proof_encodes_correctly() {
		let encoded = super::v1::light::Response {
			response: Some(super::v1::light::response::Response::RemoteReadResponse(
				super::v1::light::RemoteReadResponse { proof: None },
			)),
		}
		.encode_to_vec();

		// Make sure that the response contains one field of number 2 and wire type 2 (message).
		assert_eq!(encoded, vec![(2 << 3) | 2, 0]);
	}

	#[test]
	fn proof_encodes_correctly() {
		let encoded = super::v1::light::Response {
			response: Some(super::v1::light::response::Response::RemoteReadResponse(
				super::v1::light::RemoteReadResponse { proof: Some(vec![1, 2, 3, 4]) },
			)),
		}
		.encode_to_vec();

		assert_eq!(encoded, vec![(2 << 3) | 2, 6, (2 << 3) | 2, 4, 1, 2, 3, 4]);
	}
}
