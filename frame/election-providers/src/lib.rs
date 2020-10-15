// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Various implementation for `ElectionProvider`.
//!
//! Two main election providers are implemented in this crate.
//!
//! 1.  [`onchain`]: A `struct` that perform the election onchain (i.e. in the fly). This type is
//!     likely to be expensive for most chains and damage the block time. Only use when you are sure
//!     that the inputs are bounded and small enough.
//! 2. [`two_phase`]: An individual `pallet` that performs the election in two phases, signed and
//!    unsigned. Needless to say, the pallet needs to be included in the final runtime.

#![cfg_attr(not(feature = "std"), no_std)]

/// The onchain module.
pub mod onchain;
/// The two-phase module.
pub mod two_phase;

const LOG_TARGET: &'static str = "election-provider";

// for the helper macros
#[doc(hidden)]
pub use sp_npos_elections::VoteWeight;
#[doc(hidden)]
use sp_runtime::traits::UniqueSaturatedInto;
#[doc(hidden)]
pub use sp_std::convert::TryInto;
