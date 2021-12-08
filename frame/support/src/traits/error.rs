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
use codec::{Decode, Encode, OptionBool};
use sp_std::marker::PhantomData;

/// Trait denoting that the implementing type has the most compact encoded size that is fit to be
/// included as a field in a variant of the `#[pallet::error]` enum type.
///
/// ## Notes
/// The pallet error enum has a maximum encoded size as defined by
/// [`frame_support::MAX_PALLET_ERROR_ENCODED_SIZE`]. If the pallet error type exceeds this size
/// limit, a static assertion during compilation will fail. The compilation error will be in the
/// format of `error[E0080]: evaluation of constant value failed` due to the usage of
/// [`static_assertions::const_assert`].
pub trait CompactPalletError: Encode + Decode {
	/// The maximum encoded size for the implementing type.
	///
	/// This will be used to check whether the pallet error type is less than or equal to
	/// [`frame_support::MAX_PALLET_ERROR_ENCODED_SIZE`], and if it is, a compile error will be
	/// thrown.
	const MAX_ENCODED_SIZE: usize;
}

macro_rules! impl_for_types {
	($($typ:ty),+) => {
		$(
			impl CompactPalletError for $typ {
				const MAX_ENCODED_SIZE: usize = 1;
			}
		)+
	};
}

impl_for_types!(u8, i8, bool, OptionBool);

impl<T> CompactPalletError for PhantomData<T> {
	const MAX_ENCODED_SIZE: usize = 0;
}
