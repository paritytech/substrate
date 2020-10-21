// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

/// This is the reference impelmentation of the Substrate Simple Remote
/// Signer protocol (SSRS), allowing an external server to provide the
/// cryptographic secret and signing functionality for a substrate-based
/// chain to work. For that the node (client) connects via HTTP or Websocket
/// to the external server and calls the defined json-rpc-interface over
/// that connection.

/// This crate can be build with the `server` and `client`-features, both
/// are enabled by default. You can disable them by setting
/// `default-features = false`, then you'll only have the JSON-RPC interface
/// exposed – allowing others to provide their own type-safe implementation
/// of it.

use jsonrpc_derive::rpc;
use jsonrpc_core::BoxFuture;

use serde;

use sp_core::{
	crypto::{KeyTypeId, CryptoTypePublicPair},
	ed25519, sr25519, ecdsa
};
use sp_keystore::{
	vrf::{VRFSignature, VRFTranscriptData, VRFTranscriptValue},
};

#[cfg(feature = "server")]
pub mod server;

#[cfg(feature = "client")]
pub mod client;

/// Wrap VRFTranscriptData into a serializable format
#[derive(serde::Serialize, serde::Deserialize)]
pub struct TransferableVRFTranscriptData {
	/// The transcript's label
	pub label: Vec<u8>,
	/// Additional data to be registered into the transcript
	pub items: Vec<VRFTranscriptValue>,
}

impl From<VRFTranscriptData> for TransferableVRFTranscriptData {
	fn from(d: VRFTranscriptData) -> TransferableVRFTranscriptData {
		TransferableVRFTranscriptData {
			label: d.label.to_vec(),
			items:  d.items.into_iter().map(|(_k, v)| v).collect()
		}
	}
}

/// Simple Substrate Remote Signer JSON RPC interface
/// matches `sp-core::CryptoStore`
#[rpc]
pub trait RemoteSignerApi {

	/// Returns all sr25519 public keys for the given key type.
	#[rpc(name="signer_sr25519_public_keys", returns = "Vec<sr25519::Public>")]
	fn sr25519_public_keys(&self, id: KeyTypeId) -> BoxFuture<Vec<sr25519::Public>>;

	/// Generate a new sr25519 key pair for the given key type and an optional seed.
	///
	/// If the given seed is `Some(_)`, the key pair will only be stored in memory.
	///
	/// Returns the public key of the generated key pair.
	#[rpc(name="signer_sr25519_generate_new", returns = "sr25519::Public")]
	fn sr25519_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<String>,
	) -> BoxFuture<sr25519::Public>;

	/// Returns all ed25519 public keys for the given key type.
	#[rpc(name="signer_ed25519_public_keys", returns = "Vec<ed25519::Public>")]
	fn ed25519_public_keys(&self, id: KeyTypeId) -> BoxFuture<Vec<ed25519::Public>>;

	/// Generate a new ed25519 key pair for the given key type and an optional seed.
	///
	/// If the given seed is `Some(_)`, the key pair will only be stored in memory.
	///
	/// Returns the public key of the generated key pair.
	#[rpc(name="signer_ed25519_generate_new", returns = "ed25519::Public")]
	fn ed25519_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<String>,
	) -> BoxFuture<ed25519::Public>;

	/// Returns all ecdsa public keys for the given key type.
	#[rpc(name="signer_ecdsa_public_keys", returns = "Vec<ecdsa::Public>")]
	fn ecdsa_public_keys(&self, id: KeyTypeId) -> BoxFuture<Vec<ecdsa::Public>>;

	/// Generate a new ecdsa key pair for the given key type and an optional seed.
	///
	/// If the given seed is `Some(_)`, the key pair will only be stored in memory.
	///
	/// Returns the public key of the generated key pair.
	#[rpc(name="signer_ecdsa_generate_new", returns = "ecdsa::Public")]
	fn ecdsa_generate_new(
		&self,
		id: KeyTypeId,
		seed: Option<String>,
	) -> BoxFuture<ecdsa::Public>;

	/// Insert a new key. This doesn't require any known of the crypto; but a public key must be
	/// manually provided.
	///
	/// Places it into the file system store.
	///
	/// `Err` if there's some sort of weird filesystem error, but should generally be `Ok`.
	#[rpc(name="signer_insert_unknown", returns = "()")]
	fn insert_unknown(&self, key_type: KeyTypeId, suri: String, public: Vec<u8>) -> BoxFuture<()>;

	/// Find intersection between provided keys and supported keys
	///
	/// Provided a list of (CryptoTypeId,[u8]) pairs, this would return
	/// a filtered set of public keys which are supported by the keystore.
	#[rpc(name="signer_supported_keys", returns = "Vec<CryptoTypePublicPair>")]
	fn supported_keys(
		&self,
		id: KeyTypeId,
		keys: Vec<CryptoTypePublicPair>
	) -> BoxFuture<Vec<CryptoTypePublicPair>>;

	/// List all supported keys
	///
	/// Returns a set of public keys the signer supports.
	#[rpc(name="signer_keys", returns = "Vec<CryptoTypePublicPair>")]
	fn keys(&self, id: KeyTypeId) -> BoxFuture<Vec<CryptoTypePublicPair>>;

	/// Checks if the private keys for the given public key and key type combinations exist.
	///
	/// Returns `true` iff all private keys could be found.
	#[rpc(name="signer_has_keys", returns = "bool")]
	fn has_keys(&self, public_keys: Vec<(Vec<u8>, KeyTypeId)>) -> BoxFuture<bool>;

	/// Sign with key
	///
	/// Signs a message with the private key that matches
	/// the public key passed.
	///
	/// Returns the SCALE encoded signature if key is found & supported,
	/// an error otherwise.
	#[rpc(name="signer_sign_with", returns = "Vec<u8>")]
	fn sign_with(
		&self,
		id: KeyTypeId,
		key: CryptoTypePublicPair,
		msg: Vec<u8>,
	) -> BoxFuture<Vec<u8>>;

	/// Sign with any key
	///
	/// Given a list of public keys, find the first supported key and
	/// sign the provided message with that key.
	///
	/// Returns a tuple of the used key and the SCALE encoded signature.
	#[rpc(name="signer_sign_with_any", returns = "(CryptoTypePublicPair, Vec<u8>)")]
	fn sign_with_any(
		&self,
		id: KeyTypeId,
		keys: Vec<CryptoTypePublicPair>,
		msg: Vec<u8>,
	) -> BoxFuture<(CryptoTypePublicPair, Vec<u8>)>;

	/// Sign with all keys
	///
	/// Provided a list of public keys, sign a message with
	/// each key given that the key is supported.
	///
	/// Returns a list of `BoxFuture`s each representing the SCALE encoded
	/// signature of each key or a Error for non-supported keys.
	#[rpc(name="signer_sign_with_all", returns = "Vec<Result<Vec<u8>, String>>")]
	fn sign_with_all(
		&self,
		id: KeyTypeId,
		keys: Vec<CryptoTypePublicPair>,
		msg: Vec<u8>,
	) -> BoxFuture<Vec<Result<Vec<u8>, String>>>;

	/// Generate VRF signature for given transcript data.
	///
	/// Receives KeyTypeId and Public key to be able to map
	/// them to a private key that exists in the keystore which
	/// is, in turn, used for signing the provided transcript.
	///
	/// Returns a result containing the signature data.
	/// Namely, VRFOutput and VRFProof which are returned
	/// inside the `VRFSignature` container struct.
	///
	/// This function will return an error in the cases where
	/// the public key and key type provided do not match a private
	/// key in the keystore. Or, in the context of remote signing
	/// an error could be a network one.
	#[rpc(name="signer_sr25519_vrf_sign", returns = "VRFSignature")]
	fn sr25519_vrf_sign(
		&self,
		key_type: KeyTypeId,
		public: sr25519::Public,
		transcript_data: TransferableVRFTranscriptData,
	) -> BoxFuture<VRFSignature>;
}
