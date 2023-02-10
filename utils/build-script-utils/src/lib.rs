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

//! Crate with utility functions for `build.rs` scripts.

mod git;
mod version;
mod build_date;

pub use git::*;
pub use version::*;
pub use build_date::*;

/// Generate the `cargo:` key output
pub fn generate_cargo_keys() {
	generate_git_commit_key();
	generate_build_date_key();
}
