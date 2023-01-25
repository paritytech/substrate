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

//! Macro for benchmarking a FRAME runtime.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
mod analysis;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_instance;
mod utils;

pub mod baseline;

#[cfg(feature = "std")]
pub use analysis::{Analysis, AnalysisChoice, BenchmarkSelector};
#[doc(hidden)]
pub use frame_support;
#[doc(hidden)]
pub use log;
#[doc(hidden)]
pub use paste;
#[doc(hidden)]
pub use sp_core::defer;
#[doc(hidden)]
pub use sp_io::storage::root as storage_root;
#[doc(hidden)]
pub use sp_runtime::traits::Zero;
#[doc(hidden)]
pub use sp_runtime::StateVersion;
#[doc(hidden)]
pub use sp_std::{self, boxed::Box, prelude::Vec, str, vec};
pub use sp_storage::{well_known_keys, TrackedStorageKey};
pub use utils::*;

pub mod v1;
pub use v1::*;

pub mod v2 {
	pub use super::*;
	pub use frame_support::benchmarking::{benchmarks, *};
}
