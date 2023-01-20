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
pub mod enumerable;
pub use enumerable::InspectEnumerable;
pub mod lifetime;
pub mod metadata;
pub mod roles;

mod balanced;
mod freeze;
mod hold;
mod imbalance;
mod regular;
mod unbalanced;

pub use balanced::{Balanced, BalancedHold, DecreaseIssuance, IncreaseIssuance};
pub use freeze::{InspectFreeze, MutateFreeze};
pub use hold::{InspectHold, MutateHold};
pub use imbalance::{CreditOf, DebtOf, HandleImbalanceDrop, Imbalance};
pub use regular::{Inspect, Mutate};
pub use unbalanced::{Unbalanced, UnbalancedHold};
