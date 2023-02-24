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

//! The transaction's event returned as json compatible object.

use serde::{Deserialize, Serialize};

/// The transaction was broadcasted to a number of peers.
///
/// # Note
///
/// The RPC does not guarantee that the peers have received the
/// transaction.
///
/// When the number of peers is zero, the event guarantees that
/// shutting down the local node will lead to the transaction
/// not being included in the chain.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TransactionBroadcasted {
	/// The number of peers the transaction was broadcasted to.
	#[serde(with = "as_string")]
	pub num_peers: usize,
}

/// The transaction was included in a block of the chain.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TransactionBlock<Hash> {
	/// The hash of the block the transaction was included into.
	pub hash: Hash,
	/// The index (zero-based) of the transaction within the body of the block.
	#[serde(with = "as_string")]
	pub index: usize,
}

/// The transaction could not be processed due to an error.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TransactionError {
	/// Reason of the error.
	pub error: String,
}

/// The transaction was dropped because of exceeding limits.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TransactionDropped {
	/// True if the transaction was broadcasted to other peers and
	/// may still be included in the block.
	pub broadcasted: bool,
	/// Reason of the event.
	pub error: String,
}

/// Possible transaction status events.
///
/// The status events can be grouped based on their kinds as:
///
/// 1. Runtime validated the transaction:
/// 		- `Validated`
///
/// 2. Inside the `Ready` queue:
/// 		- `Broadcast`
///
/// 3. Leaving the pool:
/// 		- `BestChainBlockIncluded`
/// 		- `Invalid`
///
/// 4. Block finalized:
/// 		- `Finalized`
///
/// 5. At any time:
/// 		- `Dropped`
/// 		- `Error`
///
/// The subscription's stream is considered finished whenever the following events are
/// received: `Finalized`, `Error`, `Invalid` or `Dropped`. However, the user is allowed
/// to unsubscribe at any moment.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
// We need to manually specify the trait bounds for the `Hash` trait to ensure `into` and
// `from` still work.
#[serde(bound(
	serialize = "Hash: Serialize + Clone",
	deserialize = "Hash: Deserialize<'de> + Clone"
))]
#[serde(into = "TransactionEventIR<Hash>", from = "TransactionEventIR<Hash>")]
pub enum TransactionEvent<Hash> {
	/// The transaction was validated by the runtime.
	Validated,
	/// The transaction was broadcasted to a number of peers.
	Broadcasted(TransactionBroadcasted),
	/// The transaction was included in a best block of the chain.
	///
	/// # Note
	///
	/// This may contain `None` if the block is no longer a best
	/// block of the chain.
	BestChainBlockIncluded(Option<TransactionBlock<Hash>>),
	/// The transaction was included in a finalized block.
	Finalized(TransactionBlock<Hash>),
	/// The transaction could not be processed due to an error.
	Error(TransactionError),
	/// The transaction is marked as invalid.
	Invalid(TransactionError),
	/// The client was not capable of keeping track of this transaction.
	Dropped(TransactionDropped),
}

/// Intermediate representation (IR) for the transaction events
/// that handles block events only.
///
/// The block events require a JSON compatible interpretation similar to:
///
/// ```json
/// { event: "EVENT", block: { hash: "0xFF", index: 0 } }
/// ```
///
/// This IR is introduced to circumvent that the block events need to
/// be serialized/deserialized with "tag" and "content", while other
/// events only require "tag".
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "event", content = "block")]
enum TransactionEventBlockIR<Hash> {
	/// The transaction was included in the best block of the chain.
	BestChainBlockIncluded(Option<TransactionBlock<Hash>>),
	/// The transaction was included in a finalized block of the chain.
	Finalized(TransactionBlock<Hash>),
}

/// Intermediate representation (IR) for the transaction events
/// that handles non-block events only.
///
/// The non-block events require a JSON compatible interpretation similar to:
///
/// ```json
/// { event: "EVENT", num_peers: 0 }
/// ```
///
/// This IR is introduced to circumvent that the block events need to
/// be serialized/deserialized with "tag" and "content", while other
/// events only require "tag".
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "event")]
enum TransactionEventNonBlockIR {
	Validated,
	Broadcasted(TransactionBroadcasted),
	Error(TransactionError),
	Invalid(TransactionError),
	Dropped(TransactionDropped),
}

/// Intermediate representation (IR) used for serialization/deserialization of the
/// [`TransactionEvent`] in a JSON compatible format.
///
/// Serde cannot mix `#[serde(tag = "event")]` with `#[serde(tag = "event", content = "block")]`
/// for specific enum variants. Therefore, this IR is introduced to circumvent this
/// restriction, while exposing a simplified [`TransactionEvent`] for users of the
/// rust ecosystem.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(bound(serialize = "Hash: Serialize", deserialize = "Hash: Deserialize<'de>"))]
#[serde(rename_all = "camelCase")]
#[serde(untagged)]
enum TransactionEventIR<Hash> {
	Block(TransactionEventBlockIR<Hash>),
	NonBlock(TransactionEventNonBlockIR),
}

impl<Hash> From<TransactionEvent<Hash>> for TransactionEventIR<Hash> {
	fn from(value: TransactionEvent<Hash>) -> Self {
		match value {
			TransactionEvent::Validated =>
				TransactionEventIR::NonBlock(TransactionEventNonBlockIR::Validated),
			TransactionEvent::Broadcasted(event) =>
				TransactionEventIR::NonBlock(TransactionEventNonBlockIR::Broadcasted(event)),
			TransactionEvent::BestChainBlockIncluded(event) =>
				TransactionEventIR::Block(TransactionEventBlockIR::BestChainBlockIncluded(event)),
			TransactionEvent::Finalized(event) =>
				TransactionEventIR::Block(TransactionEventBlockIR::Finalized(event)),
			TransactionEvent::Error(event) =>
				TransactionEventIR::NonBlock(TransactionEventNonBlockIR::Error(event)),
			TransactionEvent::Invalid(event) =>
				TransactionEventIR::NonBlock(TransactionEventNonBlockIR::Invalid(event)),
			TransactionEvent::Dropped(event) =>
				TransactionEventIR::NonBlock(TransactionEventNonBlockIR::Dropped(event)),
		}
	}
}

impl<Hash> From<TransactionEventIR<Hash>> for TransactionEvent<Hash> {
	fn from(value: TransactionEventIR<Hash>) -> Self {
		match value {
			TransactionEventIR::NonBlock(status) => match status {
				TransactionEventNonBlockIR::Validated => TransactionEvent::Validated,
				TransactionEventNonBlockIR::Broadcasted(event) =>
					TransactionEvent::Broadcasted(event),
				TransactionEventNonBlockIR::Error(event) => TransactionEvent::Error(event),
				TransactionEventNonBlockIR::Invalid(event) => TransactionEvent::Invalid(event),
				TransactionEventNonBlockIR::Dropped(event) => TransactionEvent::Dropped(event),
			},
			TransactionEventIR::Block(block) => match block {
				TransactionEventBlockIR::Finalized(event) => TransactionEvent::Finalized(event),
				TransactionEventBlockIR::BestChainBlockIncluded(event) =>
					TransactionEvent::BestChainBlockIncluded(event),
			},
		}
	}
}

/// Serialize and deserialize helper as string.
mod as_string {
	use super::*;
	use serde::{Deserializer, Serializer};

	pub fn serialize<S: Serializer>(data: &usize, serializer: S) -> Result<S::Ok, S::Error> {
		data.to_string().serialize(serializer)
	}

	pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<usize, D::Error> {
		String::deserialize(deserializer)?
			.parse()
			.map_err(|e| serde::de::Error::custom(format!("Parsing failed: {}", e)))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::H256;

	#[test]
	fn validated_event() {
		let event: TransactionEvent<()> = TransactionEvent::Validated;
		let ser = serde_json::to_string(&event).unwrap();

		let exp = r#"{"event":"validated"}"#;
		assert_eq!(ser, exp);

		let event_dec: TransactionEvent<()> = serde_json::from_str(exp).unwrap();
		assert_eq!(event_dec, event);
	}

	#[test]
	fn broadcasted_event() {
		let event: TransactionEvent<()> =
			TransactionEvent::Broadcasted(TransactionBroadcasted { num_peers: 2 });
		let ser = serde_json::to_string(&event).unwrap();

		let exp = r#"{"event":"broadcasted","numPeers":"2"}"#;
		assert_eq!(ser, exp);

		let event_dec: TransactionEvent<()> = serde_json::from_str(exp).unwrap();
		assert_eq!(event_dec, event);
	}

	#[test]
	fn best_chain_event() {
		let event: TransactionEvent<()> = TransactionEvent::BestChainBlockIncluded(None);
		let ser = serde_json::to_string(&event).unwrap();

		let exp = r#"{"event":"bestChainBlockIncluded","block":null}"#;
		assert_eq!(ser, exp);

		let event_dec: TransactionEvent<()> = serde_json::from_str(exp).unwrap();
		assert_eq!(event_dec, event);

		let event: TransactionEvent<H256> =
			TransactionEvent::BestChainBlockIncluded(Some(TransactionBlock {
				hash: H256::from_low_u64_be(1),
				index: 2,
			}));
		let ser = serde_json::to_string(&event).unwrap();

		let exp = r#"{"event":"bestChainBlockIncluded","block":{"hash":"0x0000000000000000000000000000000000000000000000000000000000000001","index":"2"}}"#;
		assert_eq!(ser, exp);

		let event_dec: TransactionEvent<H256> = serde_json::from_str(exp).unwrap();
		assert_eq!(event_dec, event);
	}

	#[test]
	fn finalized_event() {
		let event: TransactionEvent<H256> = TransactionEvent::Finalized(TransactionBlock {
			hash: H256::from_low_u64_be(1),
			index: 10,
		});
		let ser = serde_json::to_string(&event).unwrap();

		let exp = r#"{"event":"finalized","block":{"hash":"0x0000000000000000000000000000000000000000000000000000000000000001","index":"10"}}"#;
		assert_eq!(ser, exp);

		let event_dec: TransactionEvent<H256> = serde_json::from_str(exp).unwrap();
		assert_eq!(event_dec, event);
	}

	#[test]
	fn error_event() {
		let event: TransactionEvent<()> =
			TransactionEvent::Error(TransactionError { error: "abc".to_string() });
		let ser = serde_json::to_string(&event).unwrap();

		let exp = r#"{"event":"error","error":"abc"}"#;
		assert_eq!(ser, exp);

		let event_dec: TransactionEvent<()> = serde_json::from_str(exp).unwrap();
		assert_eq!(event_dec, event);
	}

	#[test]
	fn invalid_event() {
		let event: TransactionEvent<()> =
			TransactionEvent::Invalid(TransactionError { error: "abc".to_string() });
		let ser = serde_json::to_string(&event).unwrap();

		let exp = r#"{"event":"invalid","error":"abc"}"#;
		assert_eq!(ser, exp);

		let event_dec: TransactionEvent<()> = serde_json::from_str(exp).unwrap();
		assert_eq!(event_dec, event);
	}

	#[test]
	fn dropped_event() {
		let event: TransactionEvent<()> = TransactionEvent::Dropped(TransactionDropped {
			broadcasted: true,
			error: "abc".to_string(),
		});
		let ser = serde_json::to_string(&event).unwrap();

		let exp = r#"{"event":"dropped","broadcasted":true,"error":"abc"}"#;
		assert_eq!(ser, exp);

		let event_dec: TransactionEvent<()> = serde_json::from_str(exp).unwrap();
		assert_eq!(event_dec, event);
	}
}
