// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

use sp_core::crypto::CryptoTypePublicPair;

/// AuthorityDiscovery Result.
pub type Result<T> = std::result::Result<T, Error>;

/// Error type for the authority discovery module.
#[derive(Debug, derive_more::Display, derive_more::From)]
pub enum Error {
	/// Received dht value found event with records with different keys.
	ReceivingDhtValueFoundEventWithDifferentKeys,
	/// Received dht value found event with no records.
	ReceivingDhtValueFoundEventWithNoRecords,
	/// Failed to verify a dht payload with the given signature.
	VerifyingDhtPayload,
	/// Failed to hash the authority id to be used as a dht key.
	HashingAuthorityId(libp2p::core::multiaddr::multihash::Error),
	/// Failed calling into the Substrate runtime.
	CallingRuntime(sp_blockchain::Error),
	/// Received a dht record with a key that does not match any in-flight awaited keys.
	ReceivingUnexpectedRecord,
	/// Failed to encode a protobuf payload.
	EncodingProto(prost::EncodeError),
	/// Failed to decode a protobuf payload.
	DecodingProto(prost::DecodeError),
	/// Failed to encode or decode scale payload.
	EncodingDecodingScale(codec::Error),
	/// Failed to parse a libp2p multi address.
	ParsingMultiaddress(libp2p::core::multiaddr::Error),
	/// Failed to parse a libp2p key.
	ParsingLibp2pIdentity(sc_network::DecodingError),
	/// Failed to sign using a specific public key.
	MissingSignature(CryptoTypePublicPair),
	/// Failed to sign using all public keys.
	Signing,
	/// Failed to register Prometheus metric.
	Prometheus(prometheus_endpoint::PrometheusError),
	/// Received authority record that contains addresses with multiple peer ids
	ReceivingDhtValueFoundEventWithDifferentPeerIds,
	/// Received authority record without any addresses having a peer id
	ReceivingDhtValueFoundEventWithNoPeerIds,
	/// Received authority record without a valid signature for the remote peer id.
	MissingPeerIdSignature,
}
