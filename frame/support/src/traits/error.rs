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
/// The pallet error enum has a maximum nested depth as defined by
/// [`frame_support::MAX_NESTED_PALLET_ERROR_DEPTH`]. If the pallet error type exceeds this size
/// limit, the encoded representation of it will truncate any excess bytes when setting the error
/// field during the creation of the [`DispatchError`] type.
pub trait CompactPalletError: Encode + Decode {
	/// The maximum encoded size for the implementing type.
	///
	/// This will be used to check whether the pallet error type is less than or equal to
	/// [`frame_support::MAX_NESTED_PALLET_ERROR_DEPTH`], and if it is, a compile error will be
	/// thrown.
	const MAX_ENCODED_SIZE: usize;
	/// Function that checks whether implementing types are either 1 bytes in size, or that its
	/// nested types are 1 bytes in size, i.e. whether they are as memory efficient as possible.
	///
	/// It is up to the implementing type to prove that it is maximally compact, thus this
	/// function defaults to false.
	fn check_compactness() -> bool {
		false
	}
}

macro_rules! impl_for_types {
	($($typ:ty),+) => {
		$(
			impl CompactPalletError for $typ {
				const MAX_ENCODED_SIZE: usize = 1;
				fn check_compactness() -> bool { true }
			}
		)+
	};
}

impl_for_types!(u8, i8, bool, OptionBool);

impl<T> CompactPalletError for PhantomData<T> {
	const MAX_ENCODED_SIZE: usize = 0;
	fn check_compactness() -> bool {
		true
	}
}

/// Trait for testing the pallet's error enum compactness.
pub trait ErrorCompactnessTest {
	/// The function that gets called during integrity testing to check for the compactness
	/// of the pallet's error enum type.
	fn error_compactness_test() {}
}

// This can happen in tests where no additional pallets aside from the System pallet is included
// in the runtime
impl ErrorCompactnessTest for () {}

impl<A: ErrorCompactnessTest> ErrorCompactnessTest for (A,) {
	fn error_compactness_test() {
		A::error_compactness_test();
	}
}

impl<A: ErrorCompactnessTest, B: ErrorCompactnessTest> ErrorCompactnessTest for (A, B) {
	fn error_compactness_test() {
		A::error_compactness_test();
		B::error_compactness_test();
	}
}
