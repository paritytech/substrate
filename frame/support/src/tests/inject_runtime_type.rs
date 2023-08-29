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

use super::{Config, Runtime};
use crate::{derive_impl, pallet_prelude::inject_runtime_type};
use static_assertions::assert_type_eq_all;

#[docify::export]
#[test]
fn derive_impl_works_with_runtime_type_injection() {
	assert_type_eq_all!(<Runtime as Config>::RuntimeOrigin, super::RuntimeOrigin);
	assert_type_eq_all!(<Runtime as Config>::RuntimeCall, super::RuntimeCall);
	assert_type_eq_all!(<Runtime as Config>::PalletInfo, super::PalletInfo);
}

#[docify::export]
#[test]
fn derive_impl_works_with_no_aggregated_types() {
	struct DummyRuntime;

	#[derive_impl(
        super::frame_system::config_preludes::TestDefaultConfig as super::frame_system::DefaultConfig,
        no_aggregated_types
    )]
	impl Config for DummyRuntime {
		type Block = super::Block;
		type AccountId = super::AccountId;
		type PalletInfo = super::PalletInfo;
	}

	assert_type_eq_all!(<DummyRuntime as Config>::RuntimeOrigin, ());
	assert_type_eq_all!(<DummyRuntime as Config>::RuntimeCall, ());
}
