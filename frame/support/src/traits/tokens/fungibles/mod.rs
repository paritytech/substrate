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

//! The traits for sets of fungible tokens and any associated types.

pub mod approvals;
mod enumerable;
pub mod freeze;
pub mod hold;
mod imbalance;
mod lifetime;
pub mod metadata;
mod regular;
pub mod roles;

pub use enumerable::Inspect as InspectEnumerable;
pub use freeze::{Inspect as InspectFreeze, Mutate as MutateFreeze};
pub use hold::{
	Balanced as BalancedHold, Inspect as InspectHold, Mutate as MutateHold,
	Unbalanced as UnbalancedHold,
};
pub use imbalance::{Credit, Debt, HandleImbalanceDrop, Imbalance};
pub use lifetime::{Create, Destroy};
pub use regular::{
	Balanced, DecreaseIssuance, Dust, IncreaseIssuance, Inspect, Mutate, SwapForNative, Unbalanced,
};
