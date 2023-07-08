// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

#![cfg(test)]

use crate::{mock::*, Error};
use frame_support::{assert_noop, assert_ok};

#[test]
fn bitvec_size() {
	use bitvec::BitArr;
	type CoreParts = BitArr!(for 80, in u8);
	new_test_ext().execute_with(|| {
		println!("{}", core::mem::size_of::<CoreParts>());
		panic!();
	});
}
