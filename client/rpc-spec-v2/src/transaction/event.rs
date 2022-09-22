// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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
	pub num_peers: usize,
}

/// The transaction was included in a block of the chain.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct TransactionBlock<Hash> {
	/// The hash of the block the transaction was included into.
	pub hash: Hash,
	/// The index (zero-based) of the transaction within the body of the block.
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

/// Intermediate representation (IR) for the transaction events
/// that handles block events only.
///
/// The block events require a JSON compatible interpretation similar to:
///
/// ```sh
/// { event: "EVENT", block: { hash: "0xFF", index: 0 } }
/// ```
///
/// This IR is introduced to circumvent that the block events need to
/// be serialized/deserialized with "tag" and "content", while other
/// events only require "tag".
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "event", content = "block")]
pub(crate) enum TransactionEventBlock<Hash> {
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
/// ```sh
/// { event: "EVENT", num_peers: 0 }
/// ```
///
/// This IR is introduced to circumvent that the block events need to
/// be serialized/deserialized with "tag" and "content", while other
/// events only require "tag".
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "event")]
pub(crate) enum TransactionEventNonBlock {
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
pub(crate) enum TransactionEventIR<Hash> {
	Block(TransactionEventBlock<Hash>),
	NonBlock(TransactionEventNonBlock),
}
