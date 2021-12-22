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

//! Traits for describing and constraining pallet error types.
use codec::{Decode, Encode};
use sp_std::marker::PhantomData;

/// Trait indicating that the implementing type is going to be included as a field in a variant of
/// the `#[pallet::error]` enum type.
///
/// ## Notes
/// The pallet error enum has a maximum encoded size as defined by
/// [`frame_support::MAX_PALLET_ERROR_ENCODED_SIZE`]. If the pallet error type exceeds this size
/// limit, a static assertion during compilation will fail. The compilation error will be in the
/// format of `error[E0080]: evaluation of constant value failed` due to the usage of
/// [`static_assertions::const_assert`].
pub trait PalletError: Encode + Decode {
	/// The maximum encoded size for the implementing type.
	///
	/// This will be used to check whether the pallet error type is less than or equal to
	/// [`frame_support::MAX_PALLET_ERROR_ENCODED_SIZE`], and if it is, a compilation error will be
	/// thrown.
	const MAX_ENCODED_SIZE: usize;
}

macro_rules! impl_for_types {
	(size: $size:expr, $($typ:ty),+) => {
		$(
			impl PalletError for $typ {
				const MAX_ENCODED_SIZE: usize = $size;
			}
		)+
	};
}

impl_for_types!(size: 0, ());
impl_for_types!(size: 1, u8, i8, bool);
impl_for_types!(size: 2, u16, i16);
impl_for_types!(size: 4, u32, i32);
impl_for_types!(size: 8, u64, i64);
// Contains a u64 for secs and u32 for nanos, hence 12 bytes
impl_for_types!(size: 12, core::time::Duration);
impl_for_types!(size: 16, u128, i128);

impl<T> PalletError for PhantomData<T> {
	const MAX_ENCODED_SIZE: usize = 0;
}

impl<T: PalletError> PalletError for core::ops::Range<T> {
	const MAX_ENCODED_SIZE: usize = 2 * T::MAX_ENCODED_SIZE;
}

impl<T: PalletError, const N: usize> PalletError for [T; N] {
	const MAX_ENCODED_SIZE: usize = T::MAX_ENCODED_SIZE * N;
}

impl<T: PalletError> PalletError for Option<T> {
	const MAX_ENCODED_SIZE: usize = 1 + T::MAX_ENCODED_SIZE;
}

impl<T: PalletError, E: PalletError> PalletError for Result<T, E> {
	const MAX_ENCODED_SIZE: usize = 1 + if T::MAX_ENCODED_SIZE > E::MAX_ENCODED_SIZE {
		T::MAX_ENCODED_SIZE
	} else {
		E::MAX_ENCODED_SIZE
	};
}

#[impl_trait_for_tuples::impl_for_tuples(1, 18)]
impl PalletError for Tuple {
	for_tuples!( const MAX_ENCODED_SIZE: usize = #(Tuple::MAX_ENCODED_SIZE)+*; );
}
