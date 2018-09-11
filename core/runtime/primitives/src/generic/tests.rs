// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Tests for the generic implementations of Extrinsic/Header/Block.

use codec::{Decode, Encode};
use substrate_primitives::{H256, H512};
use super::{Digest, Header, DigestItem, UncheckedExtrinsic};

type Block = super::Block<
	Header<u64, ::traits::BlakeTwo256, DigestItem<u32>>,
	UncheckedExtrinsic<H256, u64, u64, ::Ed25519Signature>,
>;

#[test]
fn block_roundtrip_serialization() {
	let block: Block = Block {
		header: Header {
			parent_hash: [0u8; 32].into(),
			number: 100_000,
			state_root: [1u8; 32].into(),
			extrinsics_root: [2u8; 32].into(),
			digest: Digest { logs: vec![
				DigestItem::Other::<u32>(vec![1, 2, 3]),
				DigestItem::Other::<u32>(vec![4, 5, 6]),
			] },
		},
		extrinsics: vec![
			UncheckedExtrinsic::new_signed(
				0,
				100,
				[255u8; 32].into(),
				H512::from([0u8; 64]).into()
			),
			UncheckedExtrinsic::new_signed(
				100,
				99,
				[128u8; 32].into(),
				H512::from([255u8; 64]).into()
			)
		]
	};

	{
		let encoded = ::serde_json::to_vec(&block).unwrap();
		let decoded: Block = ::serde_json::from_slice(&encoded).unwrap();

		assert_eq!(block, decoded);
	}
	{
		let encoded = block.encode();
		let decoded = Block::decode(&mut &encoded[..]).unwrap();

		assert_eq!(block, decoded);
	}
}

#[test]
fn system_digest_item_encoding() {
	let item = DigestItem::AuthoritiesChange::<u32>(vec![10, 20, 30]);
	let encoded = item.encode();
	assert_eq!(encoded, vec![
		// type = DigestItemType::AuthoritiesChange
		1,
		// number of items in athorities set
		3, 0, 0, 0,
		// authorities
		10, 0, 0, 0,
		20, 0, 0, 0,
		30, 0, 0, 0,
	]);

	let decoded: DigestItem<u32> = Decode::decode(&mut &encoded[..]).unwrap();
	assert_eq!(item, decoded);
}

#[test]
fn non_system_digest_item_encoding() {
	let item = DigestItem::Other::<u32>(vec![10, 20, 30]);
	let encoded = item.encode();
	assert_eq!(encoded, vec![
		// type = DigestItemType::Other
		0,
		// length of other data
		3, 0, 0, 0,
		// authorities
		10, 20, 30,
	]);

	let decoded: DigestItem<u32> = Decode::decode(&mut &encoded[..]).unwrap();
	assert_eq!(item, decoded);
}