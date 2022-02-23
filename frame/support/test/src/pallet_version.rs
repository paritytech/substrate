// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use frame_support::{crate_to_pallet_version, traits::PalletVersion};

#[test]
fn ensure_that_current_pallet_version_is_correct() {
	let expected = PalletVersion {
		major: env!("CARGO_PKG_VERSION_MAJOR").parse().unwrap(),
		minor: env!("CARGO_PKG_VERSION_MINOR").parse().unwrap(),
		patch: env!("CARGO_PKG_VERSION_PATCH").parse().unwrap(),
	};

	assert_eq!(expected, crate_to_pallet_version!())
}
