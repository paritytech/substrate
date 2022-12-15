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

mod schema_v1 {
	include!(concat!(env!("OUT_DIR"), "/authority_discovery_v1.rs"));
}

use super::*;
use libp2p::{multiaddr::Multiaddr, PeerId};
use prost::Message;

#[test]
fn v2_decodes_v1() {
	let peer_id = PeerId::random();
	let multiaddress: Multiaddr =
		format!("/ip4/127.0.0.1/tcp/3003/p2p/{}", peer_id).parse().unwrap();
	let vec_addresses = vec![multiaddress.to_vec()];
	let vec_auth_signature = b"Totally valid signature, I promise!".to_vec();

	let addresses_v1 = schema_v1::AuthorityAddresses { addresses: vec_addresses.clone() };
	let mut vec_addresses_v1 = vec![];
	addresses_v1.encode(&mut vec_addresses_v1).unwrap();
	let signed_addresses_v1 = schema_v1::SignedAuthorityAddresses {
		addresses: vec_addresses_v1.clone(),
		signature: vec_auth_signature.clone(),
	};
	let mut vec_signed_addresses_v1 = vec![];
	signed_addresses_v1.encode(&mut vec_signed_addresses_v1).unwrap();

	let signed_record_v2_decoded =
		SignedAuthorityRecord::decode(vec_signed_addresses_v1.as_slice()).unwrap();

	assert_eq!(&signed_record_v2_decoded.record, &vec_addresses_v1);
	assert_eq!(&signed_record_v2_decoded.auth_signature, &vec_auth_signature);
	assert_eq!(&signed_record_v2_decoded.peer_signature, &None);

	let record_v2_decoded = AuthorityRecord::decode(vec_addresses_v1.as_slice()).unwrap();
	assert_eq!(&record_v2_decoded.addresses, &vec_addresses);
}

#[test]
fn v1_decodes_v2() {
	let peer_secret = libp2p::identity::Keypair::generate_ed25519();
	let peer_public = peer_secret.public();
	let peer_id = peer_public.to_peer_id();
	let multiaddress: Multiaddr =
		format!("/ip4/127.0.0.1/tcp/3003/p2p/{}", peer_id).parse().unwrap();
	let vec_addresses = vec![multiaddress.to_vec()];
	let vec_auth_signature = b"Totally valid signature, I promise!".to_vec();
	let vec_peer_signature = b"Surprisingly hard to crack crypto".to_vec();

	let record_v2 = AuthorityRecord { addresses: vec_addresses.clone() };
	let mut vec_record_v2 = vec![];
	record_v2.encode(&mut vec_record_v2).unwrap();
	let vec_peer_public = peer_public.to_protobuf_encoding();
	let peer_signature_v2 =
		PeerSignature { public_key: vec_peer_public, signature: vec_peer_signature };
	let signed_record_v2 = SignedAuthorityRecord {
		record: vec_record_v2.clone(),
		auth_signature: vec_auth_signature.clone(),
		peer_signature: Some(peer_signature_v2.clone()),
	};
	let mut vec_signed_record_v2 = vec![];
	signed_record_v2.encode(&mut vec_signed_record_v2).unwrap();

	let signed_addresses_v1_decoded =
		schema_v1::SignedAuthorityAddresses::decode(vec_signed_record_v2.as_slice()).unwrap();

	assert_eq!(&signed_addresses_v1_decoded.addresses, &vec_record_v2);
	assert_eq!(&signed_addresses_v1_decoded.signature, &vec_auth_signature);

	let addresses_v2_decoded = AuthorityRecord::decode(vec_record_v2.as_slice()).unwrap();
	assert_eq!(&addresses_v2_decoded.addresses, &vec_addresses);
}
