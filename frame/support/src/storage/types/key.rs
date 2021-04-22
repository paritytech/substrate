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
use paste::paste;
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

/// A trait that contains the current key as an associated type.
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

/// Trait indicating whether a KeyGenerator has the prefix P.
pub trait HasKeyPrefix<P>: KeyGenerator {
	type Suffix;

	fn partial_key(prefix: P) -> Vec<u8>;
}

/// Trait indicating whether a ReversibleKeyGenerator has the prefix P.
pub trait HasReversibleKeyPrefix<P>: ReversibleKeyGenerator + HasKeyPrefix<P> {
	fn decode_partial_key(key_material: &[u8]) -> Result<Self::Suffix, codec::Error>;
}

macro_rules! impl_key_prefix_for {
	(($($keygen:ident),+), ($($prefix:ident),+), ($($suffix:ident),+)) => {
		paste! {
			impl<$($keygen: FullCodec,)+ $( [<$keygen $keygen>]: StorageHasher),+>
				HasKeyPrefix<($($prefix),+)> for
				($(Key<[<$keygen $keygen>], $keygen>),+)
			{
				type Suffix = ($($suffix),+);

				fn partial_key(prefix: ($($prefix),+)) -> Vec<u8> {
					<($(Key<[<$prefix $prefix>], $prefix>),+)>::final_key(prefix)
				}
			}

			impl<$($keygen: FullCodec,)+ $( [<$keygen $keygen>]: ReversibleStorageHasher),+>
				HasReversibleKeyPrefix<($($prefix),+)> for
				($(Key<[<$keygen $keygen>], $keygen>),+)
			{
				fn decode_partial_key(key_material: &[u8]) -> Result<Self::Suffix, codec::Error> {
					<($(Key<[<$suffix $suffix>], $suffix>),+)>::decode_final_key(key_material).map(|k| k.0)
				}
			}
		}
	};
	(($($keygen:ident),+), $prefix:ident, ($($suffix:ident),+)) => {
		paste! {
			impl<$($keygen: FullCodec,)+ $( [<$keygen $keygen>]: StorageHasher),+>
				HasKeyPrefix<$prefix> for
				($(Key<[<$keygen $keygen>], $keygen>),+)
			{
				type Suffix = ($($suffix),+);

				fn partial_key(prefix: $prefix) -> Vec<u8> {
					<Key<[<$prefix $prefix>], $prefix>>::final_key(prefix)
				}
			}

			impl<$($keygen: FullCodec,)+ $( [<$keygen $keygen>]: ReversibleStorageHasher),+>
				HasReversibleKeyPrefix<$prefix> for
				($(Key<[<$keygen $keygen>], $keygen>),+)
			{
				fn decode_partial_key(key_material: &[u8]) -> Result<Self::Suffix, codec::Error> {
					<($(Key<[<$suffix $suffix>], $suffix>),+)>::decode_final_key(key_material).map(|k| k.0)
				}
			}
		}
	};
	(($($keygen:ident),+), ($($prefix:ident),+), $suffix:ident) => {
		paste! {
			impl<$($keygen: FullCodec,)+ $( [<$keygen $keygen>]: StorageHasher),+>
				HasKeyPrefix<($($prefix),+)> for
				($(Key<[<$keygen $keygen>], $keygen>),+)
			{
				type Suffix = $suffix;

				fn partial_key(prefix: ($($prefix),+)) -> Vec<u8> {
					<($(Key<[<$prefix $prefix>], $prefix>),+)>::final_key(prefix)
				}
			}

			impl<$($keygen: FullCodec,)+ $( [<$keygen $keygen>]: ReversibleStorageHasher),+>
				HasReversibleKeyPrefix<($($prefix),+)> for
				($(Key<[<$keygen $keygen>], $keygen>),+)
			{
				fn decode_partial_key(key_material: &[u8]) -> Result<Self::Suffix, codec::Error> {
					<Key<[<$suffix $suffix>], $suffix>>::decode_final_key(key_material).map(|k| k.0)
				}
			}
		}
	};
}

impl<A: FullCodec, B: FullCodec, X: StorageHasher, Y: StorageHasher> HasKeyPrefix<A> for (Key<X, A>, Key<Y, B>) {
	type Suffix = B;

	fn partial_key(prefix: A) -> Vec<u8> {
		<Key<X, A>>::final_key(prefix)
	}
}

impl<A: FullCodec, B: FullCodec, X: ReversibleStorageHasher, Y: ReversibleStorageHasher>
	HasReversibleKeyPrefix<A> for (Key<X, A>, Key<Y, B>)
{
	fn decode_partial_key(key_material: &[u8]) -> Result<B, codec::Error> {
		<Key<Y, B>>::decode_final_key(key_material).map(|k| k.0)
	}
}

impl_key_prefix_for!((A, B, C), (A, B), C);
impl_key_prefix_for!((A, B, C), A, (B, C));
impl_key_prefix_for!((A, B, C, D), (A, B, C), D);
impl_key_prefix_for!((A, B, C, D), (A, B), (C, D));
impl_key_prefix_for!((A, B, C, D), A, (B, C, D));
impl_key_prefix_for!((A, B, C, D, E), (A, B, C, D), E);
impl_key_prefix_for!((A, B, C, D, E), (A, B, C), (D, E));
impl_key_prefix_for!((A, B, C, D, E), (A, B), (C, D, E));
impl_key_prefix_for!((A, B, C, D, E), A, (B, C, D, E));
impl_key_prefix_for!((A, B, C, D, E, F), (A, B, C, D, E), F);
impl_key_prefix_for!((A, B, C, D, E, F), (A, B, C, D), (E, F));
impl_key_prefix_for!((A, B, C, D, E, F), (A, B, C), (D, E, F));
impl_key_prefix_for!((A, B, C, D, E, F), (A, B), (C, D, E, F));
impl_key_prefix_for!((A, B, C, D, E, F), A, (B, C, D, E, F));
impl_key_prefix_for!((A, B, C, D, E, F, G), (A, B, C, D, E, F), G);
impl_key_prefix_for!((A, B, C, D, E, F, G), (A, B, C, D, E), (F, G));
impl_key_prefix_for!((A, B, C, D, E, F, G), (A, B, C, D), (E, F, G));
impl_key_prefix_for!((A, B, C, D, E, F, G), (A, B, C), (D, E, F, G));
impl_key_prefix_for!((A, B, C, D, E, F, G), (A, B), (C, D, E, F, G));
impl_key_prefix_for!((A, B, C, D, E, F, G), A, (B, C, D, E, F, G));
impl_key_prefix_for!((A, B, C, D, E, F, G, H), (A, B, C, D, E, F, G), H);
impl_key_prefix_for!((A, B, C, D, E, F, G, H), (A, B, C, D, E, F), (G, H));
impl_key_prefix_for!((A, B, C, D, E, F, G, H), (A, B, C, D, E), (F, G, H));
impl_key_prefix_for!((A, B, C, D, E, F, G, H), (A, B, C, D), (E, F, G, H));
impl_key_prefix_for!((A, B, C, D, E, F, G, H), (A, B, C), (D, E, F, G, H));
impl_key_prefix_for!((A, B, C, D, E, F, G, H), (A, B), (C, D, E, F, G, H));
impl_key_prefix_for!((A, B, C, D, E, F, G, H), A, (B, C, D, E, F, G, H));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I), (A, B, C, D, E, F, G, H), I);
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I), (A, B, C, D, E, F, G), (H, I));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I), (A, B, C, D, E, F), (G, H, I));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I), (A, B, C, D, E), (F, G, H, I));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I), (A, B, C, D), (E, F, G, H, I));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I), (A, B, C), (D, E, F, G, H, I));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I), (A, B), (C, D, E, F, G, H, I));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I), A, (B, C, D, E, F, G, H, I));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J), (A, B, C, D, E, F, G, H, I), J);
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J), (A, B, C, D, E, F, G, H), (I, J));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J), (A, B, C, D, E, F, G), (H, I, J));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J), (A, B, C, D, E, F), (G, H, I, J));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J), (A, B, C, D, E), (F, G, H, I, J));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J), (A, B, C, D), (E, F, G, H, I, J));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J), (A, B, C), (D, E, F, G, H, I, J));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J), (A, B), (C, D, E, F, G, H, I, J));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J), A, (B, C, D, E, F, G, H, I, J));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K), (A, B, C, D, E, F, G, H, I, J), K);
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K), (A, B, C, D, E, F, G, H, I), (J, K));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K), (A, B, C, D, E, F, G, H), (I, J, K));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K), (A, B, C, D, E, F, G), (H, I, J, K));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K), (A, B, C, D, E, F), (G, H, I, J, K));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K), (A, B, C, D, E), (F, G, H, I, J, K));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K), (A, B, C, D), (E, F, G, H, I, J, K));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K), (A, B, C), (D, E, F, G, H, I, J, K));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K), (A, B), (C, D, E, F, G, H, I, J, K));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K), A, (B, C, D, E, F, G, H, I, J, K));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L), (A, B, C, D, E, F, G, H, I, J, K), L);
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L), (A, B, C, D, E, F, G, H, I, J), (K, L));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L), (A, B, C, D, E, F, G, H, I), (J, K, L));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L), (A, B, C, D, E, F, G, H), (I, J, K, L));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L), (A, B, C, D, E, F, G), (H, I, J, K, L));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L), (A, B, C, D, E, F), (G, H, I, J, K, L));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L), (A, B, C, D, E), (F, G, H, I, J, K, L));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L), (A, B, C, D), (E, F, G, H, I, J, K, L));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L), (A, B, C), (D, E, F, G, H, I, J, K, L));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L), (A, B), (C, D, E, F, G, H, I, J, K, L));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L), A, (B, C, D, E, F, G, H, I, J, K, L));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M), (A, B, C, D, E, F, G, H, I, J, K, L), M);
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M), (A, B, C, D, E, F, G, H, I, J, K), (L, M));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M), (A, B, C, D, E, F, G, H, I, J), (K, L, M));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M), (A, B, C, D, E, F, G, H, I), (J, K, L, M));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M), (A, B, C, D, E, F, G, H), (I, J, K, L, M));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M), (A, B, C, D, E, F, G), (H, I, J, K, L, M));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M), (A, B, C, D, E, F), (G, H, I, J, K, L, M));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M), (A, B, C, D, E), (F, G, H, I, J, K, L, M));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M), (A, B, C, D), (E, F, G, H, I, J, K, L, M));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M), (A, B, C), (D, E, F, G, H, I, J, K, L, M));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M), (A, B), (C, D, E, F, G, H, I, J, K, L, M));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M), A, (B, C, D, E, F, G, H, I, J, K, L, M));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N), (A, B, C, D, E, F, G, H, I, J, K, L, M), N);
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N), (A, B, C, D, E, F, G, H, I, J, K, L), (M, N));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N), (A, B, C, D, E, F, G, H, I, J, K), (L, M, N));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N), (A, B, C, D, E, F, G, H, I, J), (K, L, M, N));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N), (A, B, C, D, E, F, G, H, I), (J, K, L, M, N));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N), (A, B, C, D, E, F, G, H), (I, J, K, L, M, N));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N), (A, B, C, D, E, F, G), (H, I, J, K, L, M, N));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N), (A, B, C, D, E, F), (G, H, I, J, K, L, M, N));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N), (A, B, C, D, E), (F, G, H, I, J, K, L, M, N));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N), (A, B, C, D), (E, F, G, H, I, J, K, L, M, N));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N), (A, B, C), (D, E, F, G, H, I, J, K, L, M, N));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N), (A, B), (C, D, E, F, G, H, I, J, K, L, M, N));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N), A, (B, C, D, E, F, G, H, I, J, K, L, M, N));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), (A, B, C, D, E, F, G, H, I, J, K, L, M, N), O);
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), (A, B, C, D, E, F, G, H, I, J, K, L, M), (N, O));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), (A, B, C, D, E, F, G, H, I, J, K, L), (M, N, O));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), (A, B, C, D, E, F, G, H, I, J, K), (L, M, N, O));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), (A, B, C, D, E, F, G, H, I, J), (K, L, M, N, O));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), (A, B, C, D, E, F, G, H, I), (J, K, L, M, N, O));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), (A, B, C, D, E, F, G, H), (I, J, K, L, M, N, O));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), (A, B, C, D, E, F, G), (H, I, J, K, L, M, N, O));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), (A, B, C, D, E, F), (G, H, I, J, K, L, M, N, O));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), (A, B, C, D, E), (F, G, H, I, J, K, L, M, N, O));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), (A, B, C, D), (E, F, G, H, I, J, K, L, M, N, O));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), (A, B, C), (D, E, F, G, H, I, J, K, L, M, N, O));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), (A, B), (C, D, E, F, G, H, I, J, K, L, M, N, O));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), A, (B, C, D, E, F, G, H, I, J, K, L, M, N, O));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), P);
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), (A, B, C, D, E, F, G, H, I, J, K, L, M, N), (O, P));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), (A, B, C, D, E, F, G, H, I, J, K, L, M), (N, O, P));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), (A, B, C, D, E, F, G, H, I, J, K, L), (M, N, O, P));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), (A, B, C, D, E, F, G, H, I, J, K), (L, M, N, O, P));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), (A, B, C, D, E, F, G, H, I, J), (K, L, M, N, O, P));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), (A, B, C, D, E, F, G, H, I), (J, K, L, M, N, O, P));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), (A, B, C, D, E, F, G, H), (I, J, K, L, M, N, O, P));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), (A, B, C, D, E, F, G), (H, I, J, K, L, M, N, O, P));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), (A, B, C, D, E, F), (G, H, I, J, K, L, M, N, O, P));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), (A, B, C, D, E), (F, G, H, I, J, K, L, M, N, O, P));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), (A, B, C, D), (E, F, G, H, I, J, K, L, M, N, O, P));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), (A, B, C), (D, E, F, G, H, I, J, K, L, M, N, O, P));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), (A, B), (C, D, E, F, G, H, I, J, K, L, M, N, O, P));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), A, (B, C, D, E, F, G, H, I, J, K, L, M, N, O, P));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), Q);
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), (P, Q));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), (A, B, C, D, E, F, G, H, I, J, K, L, M, N), (O, P, Q));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), (A, B, C, D, E, F, G, H, I, J, K, L, M), (N, O, P, Q));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), (A, B, C, D, E, F, G, H, I, J, K, L), (M, N, O, P, Q));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), (A, B, C, D, E, F, G, H, I, J, K), (L, M, N, O, P, Q));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), (A, B, C, D, E, F, G, H, I, J), (K, L, M, N, O, P, Q));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), (A, B, C, D, E, F, G, H, I), (J, K, L, M, N, O, P, Q));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), (A, B, C, D, E, F, G, H), (I, J, K, L, M, N, O, P, Q));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), (A, B, C, D, E, F, G), (H, I, J, K, L, M, N, O, P, Q));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), (A, B, C, D, E, F), (G, H, I, J, K, L, M, N, O, P, Q));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), (A, B, C, D, E), (F, G, H, I, J, K, L, M, N, O, P, Q));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), (A, B, C, D), (E, F, G, H, I, J, K, L, M, N, O, P, Q));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), (A, B, C), (D, E, F, G, H, I, J, K, L, M, N, O, P, Q));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), (A, B), (C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), A, (B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q), R);
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P), (Q, R));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B, C, D, E, F, G, H, I, J, K, L, M, N, O), (P, Q, R));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B, C, D, E, F, G, H, I, J, K, L, M, N), (O, P, Q, R));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B, C, D, E, F, G, H, I, J, K, L, M), (N, O, P, Q, R));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B, C, D, E, F, G, H, I, J, K, L), (M, N, O, P, Q, R));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B, C, D, E, F, G, H, I, J, K), (L, M, N, O, P, Q, R));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B, C, D, E, F, G, H, I, J), (K, L, M, N, O, P, Q, R));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B, C, D, E, F, G, H, I), (J, K, L, M, N, O, P, Q, R));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B, C, D, E, F, G, H), (I, J, K, L, M, N, O, P, Q, R));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B, C, D, E, F, G), (H, I, J, K, L, M, N, O, P, Q, R));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B, C, D, E, F), (G, H, I, J, K, L, M, N, O, P, Q, R));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B, C, D, E), (F, G, H, I, J, K, L, M, N, O, P, Q, R));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B, C, D), (E, F, G, H, I, J, K, L, M, N, O, P, Q, R));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B, C), (D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), (A, B), (C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R));
impl_key_prefix_for!((A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R), A, (B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R));
