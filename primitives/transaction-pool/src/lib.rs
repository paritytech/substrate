// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Transaction pool primitives types & Runtime API.

#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

pub mod runtime_api;
#[cfg(feature = "std")]
pub mod error;
#[cfg(feature = "std")]
mod pool;

#[cfg(feature = "std")]
pub use pool::*;

pub use sp_runtime::transaction_validity::{
	TransactionLongevity, TransactionPriority, TransactionTag, TransactionSource,
};
