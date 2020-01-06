// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

use crate::codec::{Decode, Encode};
use sp_core::H256;
use super::DigestItem;

#[test]
fn system_digest_item_encoding() {
	let item = DigestItem::ChangesTrieRoot::<H256>(H256::default());
	let encoded = item.encode();
	assert_eq!(encoded, vec![
		// type = DigestItemType::ChangesTrieRoot
		2,
		// trie root
		0, 0, 0, 0,
		0, 0, 0, 0,
		0, 0, 0, 0,
		0, 0, 0, 0,
		0, 0, 0, 0,
		0, 0, 0, 0,
		0, 0, 0, 0,
		0, 0, 0, 0,
	]);

	let decoded: DigestItem<H256> = Decode::decode(&mut &encoded[..]).unwrap();
	assert_eq!(item, decoded);
}

#[test]
fn non_system_digest_item_encoding() {
	let item = DigestItem::Other::<H256>(vec![10, 20, 30]);
	let encoded = item.encode();
	assert_eq!(encoded, vec![
		// type = DigestItemType::Other
		0,
		// length of other data
		12,
		// authorities
		10, 20, 30,
	]);

	let decoded: DigestItem<H256> = Decode::decode(&mut &encoded[..]).unwrap();
	assert_eq!(item, decoded);
}
