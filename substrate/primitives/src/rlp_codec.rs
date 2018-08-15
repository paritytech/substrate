// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Polkadot Blake2b (trie) NodeCodec implementation

use elastic_array::{ElasticArray1024, ElasticArray128};
use hashdb::Hasher;
use rlp::{DecoderError, RlpStream, Rlp, Prototype};
use core::marker::PhantomData;
use patricia_trie::{NibbleSlice, NodeCodec, node::Node, ChildReference};

use hash::H256;
// When switching to Blake2, use this instead:
// use BlakeHasher;
use KeccakHasher;

/// Concrete implementation of a `NodeCodec` with Rlp encoding, generic over the `Hasher`
pub struct RlpNodeCodec<H: Hasher> {mark: PhantomData<H>}

/// Convenience type for a Keccak/Rlp flavoured NodeCodec
pub type RlpCodec = RlpNodeCodec<KeccakHasher>;
// When switching to Blake2, use this instead:
// pub type RlpCodec = RlpNodeCodec<BlakeHasher>;

impl NodeCodec<KeccakHasher> for RlpCodec {
	type Error = DecoderError;
	// When switching to Blake2, use this null node
	// 	const HASHED_NULL_NODE : H256 = H256( [0x45, 0xb0, 0xcf, 0xc2, 0x20, 0xce, 0xec, 0x5b, 0x7c, 0x1c, 0x62, 0xc4, 0xd4, 0x19, 0x3d, 0x38, 0xe4, 0xeb, 0xa4, 0x8e, 0x88, 0x15, 0x72, 0x9c, 0xe7, 0x5f, 0x9c, 0xa, 0xb0, 0xe4, 0xc1, 0xc0] );
	const HASHED_NULL_NODE : H256 = H256( [0x56, 0xe8, 0x1f, 0x17, 0x1b, 0xcc, 0x55, 0xa6, 0xff, 0x83, 0x45, 0xe6, 0x92, 0xc0, 0xf8, 0x6e, 0x5b, 0x48, 0xe0, 0x1b, 0x99, 0x6c, 0xad, 0xc0, 0x01, 0x62, 0x2f, 0xb5, 0xe3, 0x63, 0xb4, 0x21] );
	fn decode(data: &[u8]) -> ::std::result::Result<Node, Self::Error> {
		let r = Rlp::new(data);
		match r.prototype()? {
			// either leaf or extension - decode first item with NibbleSlice::???
			// and use is_leaf return to figure out which.
			// if leaf, second item is a value (is_data())
			// if extension, second item is a node (either SHA3 to be looked up and
			// fed back into this function or inline RLP which can be fed back into this function).
			Prototype::List(2) => match NibbleSlice::from_encoded(r.at(0)?.data()?) {
				(slice, true) => Ok(Node::Leaf(slice, r.at(1)?.data()?)),
				(slice, false) => Ok(Node::Extension(slice, r.at(1)?.as_raw())),
			},
			// branch - first 16 are nodes, 17th is a value (or empty).
			Prototype::List(17) => {
				let mut nodes = [&[] as &[u8]; 16];
				for i in 0..16 {
					nodes[i] = r.at(i)?.as_raw();
				}
				Ok(Node::Branch(nodes, if r.at(16)?.is_empty() { None } else { Some(r.at(16)?.data()?) }))
			},
			// an empty branch index.
			Prototype::Data(0) => Ok(Node::Empty),
			// something went wrong.
			_ => Err(DecoderError::Custom("Rlp is not valid."))
		}
	}
	fn try_decode_hash(data: &[u8]) -> Option<<KeccakHasher as Hasher>::Out> {
		let r = Rlp::new(data);
		if r.is_data() && r.size() == KeccakHasher::LENGTH {
			Some(r.as_val().expect("Hash is the correct size; qed"))
		} else {
			None
		}
	}
	fn is_empty_node(data: &[u8]) -> bool {
		Rlp::new(data).is_empty()
	}
    fn empty_node() -> ElasticArray1024<u8> {
        let mut stream = RlpStream::new();
        stream.append_empty_data();
        stream.drain()
    }

    fn leaf_node(partial: &[u8], value: &[u8]) -> ElasticArray1024<u8> {
        let mut stream = RlpStream::new_list(2);
        stream.append(&partial);
        stream.append(&value);
		stream.drain()
    }

	fn ext_node(partial: &[u8], child_ref: ChildReference<<KeccakHasher as Hasher>::Out>) -> ElasticArray1024<u8> {
        let mut stream = RlpStream::new_list(2);
        stream.append(&partial);
        match child_ref {
            ChildReference::Hash(h) => stream.append(&h),
            ChildReference::Inline(inline_data, len) => {
                let bytes = &AsRef::<[u8]>::as_ref(&inline_data)[..len];
                stream.append_raw(bytes, 1)
            },
        };
        stream.drain()
	}

	fn branch_node<I>(children: I, value: Option<ElasticArray128<u8>>) -> ElasticArray1024<u8>
	where I: IntoIterator<Item=Option<ChildReference<<KeccakHasher as Hasher>::Out>>>
    {
        let mut stream = RlpStream::new_list(17);
        for child_ref in children {
            match child_ref {
                Some(c) => match c {
                    ChildReference::Hash(h) => stream.append(&h),
                    ChildReference::Inline(inline_data, len) => {
                        let bytes = &AsRef::<[u8]>::as_ref(&inline_data)[..len];
                        stream.append_raw(bytes, 1)
                    },
                },
                None => stream.append_empty_data()
            };
        }
        if let Some(value) = value {
            stream.append(&&*value);
        } else {
            stream.append_empty_data();
        }
        stream.drain()
    }
}