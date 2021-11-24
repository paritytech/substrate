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
pub trait CompactPalletError: Encode + Decode {
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
                fn check_compactness() -> bool { true }
            }
        )+
    };
}

impl_for_types!(u8, i8, bool, OptionBool);

impl<T> CompactPalletError for PhantomData<T> {
	fn check_compactness() -> bool {
		true
	}
}

pub trait ErrorCompactnessTest {
	fn error_compactness_test() {}
}

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
