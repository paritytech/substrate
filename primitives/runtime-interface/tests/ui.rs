// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

use std::env;

#[rustversion::attr(not(stable), ignore)]
#[test]
fn ui() {
	// Only run the ui tests when `RUN_UI_TESTS` is set.
	if env::var("RUN_UI_TESTS").is_err() {
		return
	}

	// As trybuild is using `cargo check`, we don't need the real WASM binaries.
	env::set_var("SKIP_WASM_BUILD", "1");

	let t = trybuild::TestCases::new();
	t.compile_fail("tests/ui/*.rs");
}
