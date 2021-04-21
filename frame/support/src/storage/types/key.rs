// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Storage key type.

use crate::hash::{ReversibleStorageHasher, StorageHasher};
use codec::{EncodeLike, FullCodec};
use sp_std::prelude::*;

/// A type used exclusively by storage maps as their key type.
///
/// The final key generated has the following form:
/// ```nocompile
/// Hasher1(encode(key1))
///     ++ Hasher2(encode(key2))
///     ++ ...
///     ++ HasherN(encode(keyN))
/// ```
pub struct Key<Hasher, KeyType>(
	core::marker::PhantomData<(Hasher, KeyType)>,
);

/// A trait that contains the current key as an associated type and generates the next key.
pub trait KeyGenerator {
	type Key: EncodeLike<Self::Key>;

	fn final_key(key: Self::Key) -> Vec<u8>;
}

impl<H: StorageHasher, K: FullCodec> KeyGenerator for Key<H, K> {
	type Key = K;

	fn final_key(key: Self::Key) -> Vec<u8> {
		key.using_encoded(H::hash).as_ref().to_vec()
	}
}

#[impl_trait_for_tuples::impl_for_tuples(2, 18)]
impl KeyGenerator for Tuple {
	for_tuples!( type Key = ( #(Tuple::Key),* ); );

	fn final_key(key: Self::Key) -> Vec<u8> {
		let mut final_key = Vec::new();
		for_tuples!(
			#( final_key.extend_from_slice(&Tuple::final_key(key.Tuple)); )*
		);
		final_key
	}
}

/// A trait that indicates the hashers for the keys generated are all reversible.
pub trait ReversibleKeyGenerator: KeyGenerator {
	type Hasher;
	fn decode_final_key(key_material: &[u8]) -> Result<(Self::Key, &[u8]), codec::Error>;
}

impl<H: ReversibleStorageHasher, K: FullCodec> ReversibleKeyGenerator for Key<H, K> {
	type Hasher = H;

	fn decode_final_key(key_material: &[u8]) -> Result<(Self::Key, &[u8]), codec::Error> {
		let mut current_key_material = Self::Hasher::reverse(key_material);
		let key = K::decode(&mut current_key_material)?;
		Ok((key, current_key_material))
	}
}

#[impl_trait_for_tuples::impl_for_tuples(2, 18)]
impl ReversibleKeyGenerator for Tuple {
	for_tuples!( type Hasher = ( #(Tuple::Hasher),* ); );

	fn decode_final_key(key_material: &[u8]) -> Result<(Self::Key, &[u8]), codec::Error> {
		let mut current_key_material = key_material;
		Ok(((
			for_tuples!{
				#({
					let (key, material) = Tuple::decode_final_key(current_key_material)?;
					current_key_material = material;
					key
				}),*
			}
		), current_key_material))
	}
}
