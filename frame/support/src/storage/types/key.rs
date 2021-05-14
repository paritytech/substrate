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
use codec::{Encode, EncodeLike, FullCodec};
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
pub struct Key<Hasher, KeyType>(core::marker::PhantomData<(Hasher, KeyType)>);

/// A trait that contains the current key as an associated type.
pub trait KeyGenerator {
	type Key: EncodeLike<Self::Key>;
	type KArg: Encode;
	type HashFn: FnOnce(&[u8]) -> Vec<u8>;
	type HArg;

	const HASHER_METADATA: &'static [frame_metadata::StorageHasher];

	/// Given a `key` tuple, calculate the final key by encoding each element individuallly and
	/// hashing them using the corresponding hasher in the `KeyGenerator`.
	fn final_key<KArg: EncodeLikeTuple<Self::KArg> + TupleToEncodedIter>(key: KArg) -> Vec<u8>;
	/// Given a `key` tuple, migrate the keys from using the old hashers as given by `hash_fns`
	/// to using the newer hashers as specified by this `KeyGenerator`.
	fn migrate_key<KArg: EncodeLikeTuple<Self::KArg> + TupleToEncodedIter>(
		key: &KArg,
		hash_fns: Self::HArg,
	) -> Vec<u8>;
}

/// A trait containing methods that are only implemented on the Key struct instead of the entire tuple.
pub trait KeyGeneratorInner: KeyGenerator {
	type Hasher: StorageHasher;

	/// Hash a given `encoded` byte slice using the `KeyGenerator`'s associated `StorageHasher`.
	fn final_hash(encoded: &[u8]) -> Vec<u8>;
}

impl<H: StorageHasher, K: FullCodec> KeyGenerator for Key<H, K> {
	type Key = K;
	type KArg = (K,);
	type HashFn = Box<dyn FnOnce(&[u8]) -> Vec<u8>>;
	type HArg = (Self::HashFn,);

	const HASHER_METADATA: &'static [frame_metadata::StorageHasher] = &[H::METADATA];

	fn final_key<KArg: EncodeLikeTuple<Self::KArg> + TupleToEncodedIter>(key: KArg) -> Vec<u8> {
		H::hash(
			&key.to_encoded_iter()
				.next()
				.expect("should have at least one element!"),
		)
		.as_ref()
		.to_vec()
	}

	fn migrate_key<KArg: EncodeLikeTuple<Self::KArg> + TupleToEncodedIter>(
		key: &KArg,
		hash_fns: Self::HArg,
	) -> Vec<u8> {
		(hash_fns.0)(
			&key.to_encoded_iter()
				.next()
				.expect("should have at least one element!"),
		)
	}
}

impl<H: StorageHasher, K: FullCodec> KeyGeneratorInner for Key<H, K> {
	type Hasher = H;

	fn final_hash(encoded: &[u8]) -> Vec<u8> {
		H::hash(encoded).as_ref().to_vec()
	}
}

#[impl_trait_for_tuples::impl_for_tuples(2, 18)]
#[tuple_types_custom_trait_bound(KeyGeneratorInner)]
impl KeyGenerator for Tuple {
	for_tuples!( type Key = ( #(Tuple::Key),* ); );
	for_tuples!( type KArg = ( #(Tuple::Key),* ); );
	for_tuples!( type HArg = ( #(Tuple::HashFn),* ); );
	type HashFn = Box<dyn FnOnce(&[u8]) -> Vec<u8>>;

	const HASHER_METADATA: &'static [frame_metadata::StorageHasher] = &[
		for_tuples!( #(Tuple::Hasher::METADATA),* )
	];

	fn final_key<KArg: EncodeLikeTuple<Self::KArg> + TupleToEncodedIter>(key: KArg) -> Vec<u8> {
		let mut final_key = Vec::new();
		let mut iter = key.to_encoded_iter();
		for_tuples!(
			#(
				let next_encoded = iter.next().expect("KArg number should be equal to Key number");
				final_key.extend_from_slice(&Tuple::final_hash(&next_encoded));
			)*
		);
		final_key
	}

	fn migrate_key<KArg: EncodeLikeTuple<Self::KArg> + TupleToEncodedIter>(
		key: &KArg,
		hash_fns: Self::HArg,
	) -> Vec<u8> {
		let mut migrated_key = Vec::new();
		let mut iter = key.to_encoded_iter();
		for_tuples!(
			#(
				let next_encoded = iter.next().expect("KArg number should be equal to Key number");
				migrated_key.extend_from_slice(&(hash_fns.Tuple)(&next_encoded));
			)*
		);
		migrated_key
	}
}

/// Marker trait to indicate that each element in the tuple encodes like the corresponding element
/// in another tuple.
///
/// This trait is sealed.
pub trait EncodeLikeTuple<T>: crate::storage::private::Sealed {}

macro_rules! impl_encode_like_tuples {
	($($elem:ident),+) => {
		paste! {
			impl<$($elem: Encode,)+ $([<$elem $elem>]: Encode + EncodeLike<$elem>,)+>
				EncodeLikeTuple<($($elem,)+)> for
				($([<$elem $elem>],)+) {}
			impl<$($elem: Encode,)+ $([<$elem $elem>]: Encode + EncodeLike<$elem>,)+>
				EncodeLikeTuple<($($elem,)+)> for
				&($([<$elem $elem>],)+) {}
		}
	};
}

impl_encode_like_tuples!(A);
impl_encode_like_tuples!(A, B);
impl_encode_like_tuples!(A, B, C);
impl_encode_like_tuples!(A, B, C, D);
impl_encode_like_tuples!(A, B, C, D, E);
impl_encode_like_tuples!(A, B, C, D, E, F);
impl_encode_like_tuples!(A, B, C, D, E, F, G);
impl_encode_like_tuples!(A, B, C, D, E, F, G, H);
impl_encode_like_tuples!(A, B, C, D, E, F, G, H, I);
impl_encode_like_tuples!(A, B, C, D, E, F, G, H, I, J);
impl_encode_like_tuples!(A, B, C, D, E, F, G, H, I, J, K);
impl_encode_like_tuples!(A, B, C, D, E, F, G, H, I, J, K, L);
impl_encode_like_tuples!(A, B, C, D, E, F, G, H, I, J, K, L, M);
impl_encode_like_tuples!(A, B, C, D, E, F, G, H, I, J, K, L, M, O);
impl_encode_like_tuples!(A, B, C, D, E, F, G, H, I, J, K, L, M, O, P);
impl_encode_like_tuples!(A, B, C, D, E, F, G, H, I, J, K, L, M, O, P, Q);
impl_encode_like_tuples!(A, B, C, D, E, F, G, H, I, J, K, L, M, O, P, Q, R);

/// Trait to indicate that a tuple can be converted into an iterator of a vector of encoded bytes.
pub trait TupleToEncodedIter {
	fn to_encoded_iter(&self) -> sp_std::vec::IntoIter<Vec<u8>>;
}

#[impl_trait_for_tuples::impl_for_tuples(1, 18)]
#[tuple_types_custom_trait_bound(Encode)]
impl TupleToEncodedIter for Tuple {
	fn to_encoded_iter(&self) -> sp_std::vec::IntoIter<Vec<u8>> {
		[for_tuples!( #(self.Tuple.encode()),* )]
			.to_vec()
			.into_iter()
	}
}

impl<T: TupleToEncodedIter> TupleToEncodedIter for &T {
	fn to_encoded_iter(&self) -> sp_std::vec::IntoIter<Vec<u8>> {
		(*self).to_encoded_iter()
	}
}

/// A trait that indicates the hashers for the keys generated are all reversible.
pub trait ReversibleKeyGenerator: KeyGenerator {
	type ReversibleHasher;
	fn decode_final_key(key_material: &[u8]) -> Result<(Self::Key, &[u8]), codec::Error>;
}

impl<H: ReversibleStorageHasher, K: FullCodec> ReversibleKeyGenerator for Key<H, K> {
	type ReversibleHasher = H;

	fn decode_final_key(key_material: &[u8]) -> Result<(Self::Key, &[u8]), codec::Error> {
		let mut current_key_material = Self::ReversibleHasher::reverse(key_material);
		let key = K::decode(&mut current_key_material)?;
		Ok((key, current_key_material))
	}
}

#[impl_trait_for_tuples::impl_for_tuples(2, 18)]
#[tuple_types_custom_trait_bound(ReversibleKeyGenerator + KeyGeneratorInner)]
impl ReversibleKeyGenerator for Tuple {
	for_tuples!( type ReversibleHasher = ( #(Tuple::ReversibleHasher),* ); );

	fn decode_final_key(key_material: &[u8]) -> Result<(Self::Key, &[u8]), codec::Error> {
		let mut current_key_material = key_material;
		Ok((
			(for_tuples! {
				#({
					let (key, material) = Tuple::decode_final_key(current_key_material)?;
					current_key_material = material;
					key
				}),*
			}),
			current_key_material,
		))
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
			impl<
				$($keygen: FullCodec,)+
				$( [<$keygen $keygen>]: StorageHasher,)+
				$( [<KArg $prefix>]: EncodeLike<$prefix> ),+
			> HasKeyPrefix<($( [<KArg $prefix>] ),+)> for ($(Key<[<$keygen $keygen>], $keygen>),+) {
				type Suffix = ($($suffix),+);

				fn partial_key(prefix: ($( [<KArg $prefix>] ),+)) -> Vec<u8> {
					<($(Key<[<$prefix $prefix>], $prefix>),+)>::final_key(prefix)
				}
			}

			impl<
				$($keygen: FullCodec,)+
				$( [<$keygen $keygen>]: ReversibleStorageHasher,)+
				$( [<KArg $prefix>]: EncodeLike<$prefix> ),+
			> HasReversibleKeyPrefix<($( [<KArg $prefix>] ),+)> for
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
			impl<
				$($keygen: FullCodec,)+
				$( [<$keygen $keygen>]: StorageHasher,)+
				[<KArg $prefix>]: EncodeLike<$prefix>
			> HasKeyPrefix<( [<KArg $prefix>] ,)> for ($(Key<[<$keygen $keygen>], $keygen>),+) {
				type Suffix = ($($suffix),+);

				fn partial_key(prefix: ( [<KArg $prefix>] ,)) -> Vec<u8> {
					<Key<[<$prefix $prefix>], $prefix>>::final_key(prefix)
				}
			}

			impl<
				$($keygen: FullCodec,)+
				$( [<$keygen $keygen>]: ReversibleStorageHasher,)+
				[<KArg $prefix>]: EncodeLike<$prefix>
			> HasReversibleKeyPrefix<( [<KArg $prefix>] ,)> for
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
			impl<
				$($keygen: FullCodec,)+
				$( [<$keygen $keygen>]: StorageHasher,)+
				$( [<KArg $prefix>]: EncodeLike<$prefix>),+
			> HasKeyPrefix<($( [<KArg $prefix>] ),+)> for ($(Key<[<$keygen $keygen>], $keygen>),+) {
				type Suffix = $suffix;

				fn partial_key(prefix: ($( [<KArg $prefix>] ),+)) -> Vec<u8> {
					<($(Key<[<$prefix $prefix>], $prefix>),+)>::final_key(prefix)
				}
			}

			impl<
				$($keygen: FullCodec,)+
				$( [<$keygen $keygen>]: ReversibleStorageHasher,)+
				$( [<KArg $prefix>]: EncodeLike<$prefix> ),+
			> HasReversibleKeyPrefix<($( [<KArg $prefix>] ),+)> for
				($(Key<[<$keygen $keygen>], $keygen>),+)
			{
				fn decode_partial_key(key_material: &[u8]) -> Result<Self::Suffix, codec::Error> {
					<Key<[<$suffix $suffix>], $suffix>>::decode_final_key(key_material).map(|k| k.0)
				}
			}
		}
	};
}

impl<A, B, X, Y, KArg> HasKeyPrefix<(KArg,)> for (Key<X, A>, Key<Y, B>)
where
	A: FullCodec,
	B: FullCodec,
	X: StorageHasher,
	Y: StorageHasher,
	KArg: EncodeLike<A>,
{
	type Suffix = B;

	fn partial_key(prefix: (KArg,)) -> Vec<u8> {
		<Key<X, A>>::final_key(prefix)
	}
}

impl<A, B, X, Y, KArg> HasReversibleKeyPrefix<(KArg,)> for (Key<X, A>, Key<Y, B>)
where
	A: FullCodec,
	B: FullCodec,
	X: ReversibleStorageHasher,
	Y: ReversibleStorageHasher,
	KArg: EncodeLike<A>,
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
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J),
	(A, B, C, D, E, F, G, H, I),
	J
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J),
	(A, B, C, D, E, F, G, H),
	(I, J)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J),
	(A, B, C, D, E, F, G),
	(H, I, J)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J),
	(A, B, C, D, E, F),
	(G, H, I, J)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J),
	(A, B, C, D, E),
	(F, G, H, I, J)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J),
	(A, B, C, D),
	(E, F, G, H, I, J)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J),
	(A, B, C),
	(D, E, F, G, H, I, J)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J),
	(A, B),
	(C, D, E, F, G, H, I, J)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J),
	A,
	(B, C, D, E, F, G, H, I, J)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K),
	(A, B, C, D, E, F, G, H, I, J),
	K
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K),
	(A, B, C, D, E, F, G, H, I),
	(J, K)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K),
	(A, B, C, D, E, F, G, H),
	(I, J, K)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K),
	(A, B, C, D, E, F, G),
	(H, I, J, K)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K),
	(A, B, C, D, E, F),
	(G, H, I, J, K)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K),
	(A, B, C, D, E),
	(F, G, H, I, J, K)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K),
	(A, B, C, D),
	(E, F, G, H, I, J, K)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K),
	(A, B, C),
	(D, E, F, G, H, I, J, K)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K),
	(A, B),
	(C, D, E, F, G, H, I, J, K)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K),
	A,
	(B, C, D, E, F, G, H, I, J, K)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L),
	(A, B, C, D, E, F, G, H, I, J, K),
	L
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L),
	(A, B, C, D, E, F, G, H, I, J),
	(K, L)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L),
	(A, B, C, D, E, F, G, H, I),
	(J, K, L)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L),
	(A, B, C, D, E, F, G, H),
	(I, J, K, L)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L),
	(A, B, C, D, E, F, G),
	(H, I, J, K, L)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L),
	(A, B, C, D, E, F),
	(G, H, I, J, K, L)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L),
	(A, B, C, D, E),
	(F, G, H, I, J, K, L)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L),
	(A, B, C, D),
	(E, F, G, H, I, J, K, L)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L),
	(A, B, C),
	(D, E, F, G, H, I, J, K, L)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L),
	(A, B),
	(C, D, E, F, G, H, I, J, K, L)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L),
	A,
	(B, C, D, E, F, G, H, I, J, K, L)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	(A, B, C, D, E, F, G, H, I, J, K, L),
	M
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	(A, B, C, D, E, F, G, H, I, J, K),
	(L, M)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	(A, B, C, D, E, F, G, H, I, J),
	(K, L, M)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	(A, B, C, D, E, F, G, H, I),
	(J, K, L, M)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	(A, B, C, D, E, F, G, H),
	(I, J, K, L, M)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	(A, B, C, D, E, F, G),
	(H, I, J, K, L, M)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	(A, B, C, D, E, F),
	(G, H, I, J, K, L, M)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	(A, B, C, D, E),
	(F, G, H, I, J, K, L, M)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	(A, B, C, D),
	(E, F, G, H, I, J, K, L, M)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	(A, B, C),
	(D, E, F, G, H, I, J, K, L, M)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	(A, B),
	(C, D, E, F, G, H, I, J, K, L, M)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	A,
	(B, C, D, E, F, G, H, I, J, K, L, M)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	N
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	(A, B, C, D, E, F, G, H, I, J, K, L),
	(M, N)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	(A, B, C, D, E, F, G, H, I, J, K),
	(L, M, N)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	(A, B, C, D, E, F, G, H, I, J),
	(K, L, M, N)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	(A, B, C, D, E, F, G, H, I),
	(J, K, L, M, N)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	(A, B, C, D, E, F, G, H),
	(I, J, K, L, M, N)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	(A, B, C, D, E, F, G),
	(H, I, J, K, L, M, N)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	(A, B, C, D, E, F),
	(G, H, I, J, K, L, M, N)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	(A, B, C, D, E),
	(F, G, H, I, J, K, L, M, N)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	(A, B, C, D),
	(E, F, G, H, I, J, K, L, M, N)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	(A, B, C),
	(D, E, F, G, H, I, J, K, L, M, N)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	(A, B),
	(C, D, E, F, G, H, I, J, K, L, M, N)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	A,
	(B, C, D, E, F, G, H, I, J, K, L, M, N)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	O
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	(N, O)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	(A, B, C, D, E, F, G, H, I, J, K, L),
	(M, N, O)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	(A, B, C, D, E, F, G, H, I, J, K),
	(L, M, N, O)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	(A, B, C, D, E, F, G, H, I, J),
	(K, L, M, N, O)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	(A, B, C, D, E, F, G, H, I),
	(J, K, L, M, N, O)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	(A, B, C, D, E, F, G, H),
	(I, J, K, L, M, N, O)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	(A, B, C, D, E, F, G),
	(H, I, J, K, L, M, N, O)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	(A, B, C, D, E, F),
	(G, H, I, J, K, L, M, N, O)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	(A, B, C, D, E),
	(F, G, H, I, J, K, L, M, N, O)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	(A, B, C, D),
	(E, F, G, H, I, J, K, L, M, N, O)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	(A, B, C),
	(D, E, F, G, H, I, J, K, L, M, N, O)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	(A, B),
	(C, D, E, F, G, H, I, J, K, L, M, N, O)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	A,
	(B, C, D, E, F, G, H, I, J, K, L, M, N, O)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	P
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	(O, P)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	(N, O, P)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	(A, B, C, D, E, F, G, H, I, J, K, L),
	(M, N, O, P)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	(A, B, C, D, E, F, G, H, I, J, K),
	(L, M, N, O, P)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	(A, B, C, D, E, F, G, H, I, J),
	(K, L, M, N, O, P)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	(A, B, C, D, E, F, G, H, I),
	(J, K, L, M, N, O, P)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	(A, B, C, D, E, F, G, H),
	(I, J, K, L, M, N, O, P)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	(A, B, C, D, E, F, G),
	(H, I, J, K, L, M, N, O, P)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	(A, B, C, D, E, F),
	(G, H, I, J, K, L, M, N, O, P)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	(A, B, C, D, E),
	(F, G, H, I, J, K, L, M, N, O, P)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	(A, B, C, D),
	(E, F, G, H, I, J, K, L, M, N, O, P)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	(A, B, C),
	(D, E, F, G, H, I, J, K, L, M, N, O, P)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	(A, B),
	(C, D, E, F, G, H, I, J, K, L, M, N, O, P)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	A,
	(B, C, D, E, F, G, H, I, J, K, L, M, N, O, P)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	Q
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	(P, Q)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	(O, P, Q)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	(N, O, P, Q)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	(A, B, C, D, E, F, G, H, I, J, K, L),
	(M, N, O, P, Q)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	(A, B, C, D, E, F, G, H, I, J, K),
	(L, M, N, O, P, Q)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	(A, B, C, D, E, F, G, H, I, J),
	(K, L, M, N, O, P, Q)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	(A, B, C, D, E, F, G, H, I),
	(J, K, L, M, N, O, P, Q)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	(A, B, C, D, E, F, G, H),
	(I, J, K, L, M, N, O, P, Q)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	(A, B, C, D, E, F, G),
	(H, I, J, K, L, M, N, O, P, Q)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	(A, B, C, D, E, F),
	(G, H, I, J, K, L, M, N, O, P, Q)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	(A, B, C, D, E),
	(F, G, H, I, J, K, L, M, N, O, P, Q)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	(A, B, C, D),
	(E, F, G, H, I, J, K, L, M, N, O, P, Q)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	(A, B, C),
	(D, E, F, G, H, I, J, K, L, M, N, O, P, Q)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	(A, B),
	(C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	A,
	(B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q),
	R
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P),
	(Q, R)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O),
	(P, Q, R)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N),
	(O, P, Q, R)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B, C, D, E, F, G, H, I, J, K, L, M),
	(N, O, P, Q, R)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B, C, D, E, F, G, H, I, J, K, L),
	(M, N, O, P, Q, R)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B, C, D, E, F, G, H, I, J, K),
	(L, M, N, O, P, Q, R)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B, C, D, E, F, G, H, I, J),
	(K, L, M, N, O, P, Q, R)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B, C, D, E, F, G, H, I),
	(J, K, L, M, N, O, P, Q, R)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B, C, D, E, F, G, H),
	(I, J, K, L, M, N, O, P, Q, R)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B, C, D, E, F, G),
	(H, I, J, K, L, M, N, O, P, Q, R)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B, C, D, E, F),
	(G, H, I, J, K, L, M, N, O, P, Q, R)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B, C, D, E),
	(F, G, H, I, J, K, L, M, N, O, P, Q, R)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B, C, D),
	(E, F, G, H, I, J, K, L, M, N, O, P, Q, R)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B, C),
	(D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	(A, B),
	(C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R)
);
impl_key_prefix_for!(
	(A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R),
	A,
	(B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R)
);
