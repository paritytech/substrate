// This file is part of Substrate.

// Copyright (C) 2021 Subspace Labs, Inc.
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

//! Primitives for Spartan-based PoR.
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
pub mod spartan;

/// The length of the Randomness.
pub const RANDOMNESS_LENGTH: usize = 32;

/// Randomness value.
pub type Randomness = [u8; RANDOMNESS_LENGTH];

