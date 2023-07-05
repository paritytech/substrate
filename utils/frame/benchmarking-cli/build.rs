// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::env;

/// Exposes build environment variables to the rust code.
///
/// - The build profile as `build_profile`
/// - The optimization level as `build_opt_level`
pub fn main() {
	if let Ok(opt_level) = env::var("OPT_LEVEL") {
		println!("cargo:rustc-cfg=build_opt_level={:?}", opt_level);
	}
	if let Ok(profile) = env::var("PROFILE") {
		println!("cargo:rustc-cfg=build_profile={:?}", profile);
	}
}
