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

//! On-the-wire protocol name generation helpers.

use crate::config::ProtocolId;

/// Standard protocol name on the wire based on `genesis_hash`, `fork_id`, and protocol-specific
/// `short_name`.
///
/// `short_name` must include the leading slash, e.g.: "/transactions/1".
pub fn standard_protocol_name<Hash: AsRef<[u8]>>(
	genesis_hash: Hash,
	fork_id: &Option<String>,
	short_name: &str,
) -> std::borrow::Cow<'static, str> {
	let chain_prefix = match fork_id {
		Some(fork_id) => format!("/{}/{}", hex::encode(genesis_hash), fork_id),
		None => format!("/{}", hex::encode(genesis_hash)),
	};
	format!("{}{}", chain_prefix, short_name).into()
}

/// Legacy (fallback) protocol name on the wire based on [`ProtocolId`].
pub fn legacy_protocol_name(
	protocol_id: &ProtocolId,
	short_name: &str,
) -> std::borrow::Cow<'static, str> {
	format!("/{}{}", protocol_id.as_ref(), short_name).into()
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn standard_protocol_name_test() {
		const SHORT_NAME: &str = "/protocol/1";

		// Create protocol name using random genesis hash and no fork id.
		let genesis_hash = sp_core::H256::random();
		let fork_id = None;
		let expected = format!("/{}/protocol/1", hex::encode(genesis_hash));
		let protocol_name = standard_protocol_name(genesis_hash, &fork_id, SHORT_NAME);
		assert_eq!(protocol_name.to_string(), expected);

		// Create protocol name with fork id.
		let fork_id = Some("fork".to_string());
		let expected = format!("/{}/fork/protocol/1", hex::encode(genesis_hash));
		let protocol_name = standard_protocol_name(genesis_hash, &fork_id, SHORT_NAME);
		assert_eq!(protocol_name.to_string(), expected);

		// Create protocol name using hardcoded genesis hash. Verify exact representation.
		let genesis_hash = [
			53, 79, 112, 97, 119, 217, 39, 202, 147, 138, 225, 38, 88, 182, 215, 185, 110, 88, 8,
			53, 125, 210, 158, 151, 50, 113, 102, 59, 245, 199, 221, 240,
		];
		let fork_id = None;
		let expected =
			"/354f706177d927ca938ae12658b6d7b96e5808357dd29e973271663bf5c7ddf0/protocol/1";
		let protocol_name = standard_protocol_name(genesis_hash, &fork_id, SHORT_NAME);
		assert_eq!(protocol_name.to_string(), expected.to_string());

		// Create protocol name using hardcoded genesis hash and fork_id.
		// Verify exact representation.
		let fork_id = Some("fork".to_string());
		let expected =
			"/354f706177d927ca938ae12658b6d7b96e5808357dd29e973271663bf5c7ddf0/fork/protocol/1";
		let protocol_name = standard_protocol_name(genesis_hash, &fork_id, SHORT_NAME);
		assert_eq!(protocol_name.to_string(), expected.to_string());
	}

	#[test]
	fn legacy_protocol_name_test() {
		const SHORT_NAME: &str = "/protocol/1";

		let protocol_id = ProtocolId::from("dot");
		let expected = "/dot/protocol/1";
		let legacy_name = legacy_protocol_name(&protocol_id, SHORT_NAME);
		assert_eq!(legacy_name.to_string(), expected.to_string());
	}
}
