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

//! Authority discovery errors.

/// AuthorityDiscovery Result.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type for the authority discovery module.
#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
pub enum Error {
	#[error("Received dht value found event with records with different keys.")]
	ReceivingDhtValueFoundEventWithDifferentKeys,

	#[error("Received dht value found event with no records.")]
	ReceivingDhtValueFoundEventWithNoRecords,

	#[error("Failed to verify a dht payload with the given signature.")]
	VerifyingDhtPayload,

	#[error("Failed to hash the authority id to be used as a dht key.")]
	HashingAuthorityId(#[from] libp2p::core::multiaddr::multihash::Error),

	#[error("Failed calling into the Substrate runtime: {0}")]
	CallingRuntime(#[from] sp_blockchain::Error),

	#[error("Received a dht record with a key that does not match any in-flight awaited keys.")]
	ReceivingUnexpectedRecord,

	#[error("Failed to encode a protobuf payload.")]
	EncodingProto(#[from] prost::EncodeError),

	#[error("Failed to decode a protobuf payload.")]
	DecodingProto(#[from] prost::DecodeError),

	#[error("Failed to encode or decode scale payload.")]
	EncodingDecodingScale(#[from] codec::Error),

	#[error("Failed to parse a libp2p multi address.")]
	ParsingMultiaddress(#[from] libp2p::core::multiaddr::Error),

	#[error("Failed to parse a libp2p key.")]
	ParsingLibp2pIdentity(#[from] libp2p::identity::DecodingError),

	#[error("Failed to sign: {0}.")]
	CannotSign(String),

	#[error("Failed to register Prometheus metric.")]
	Prometheus(#[from] prometheus_endpoint::PrometheusError),

	#[error("Received authority record that contains addresses with multiple peer ids")]
	ReceivingDhtValueFoundEventWithDifferentPeerIds,

	#[error("Received authority record without any addresses having a peer id")]
	ReceivingDhtValueFoundEventWithNoPeerIds,

	#[error("Received authority record without a valid signature for the remote peer id.")]
	MissingPeerIdSignature,

	#[error("Unable to fetch best block.")]
	BestBlockFetchingError,
}
