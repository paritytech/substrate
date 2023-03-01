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
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// distributed under the License is distributed on an "AS IS" BASIS,
// See the License for the specific language governing permissions and
// limitations under the License.

//! Traits for the npos-election operations.

use crate::ExtendedBalance;
use sp_arithmetic::PerThing;
use sp_std::{fmt::Debug, ops::Mul, prelude::*};

/// an aggregator trait for a generic type of a voter/target identifier. This usually maps to
/// substrate's account id.
pub trait IdentifierT: Clone + Eq + Ord + Debug + codec::Codec {}
impl<T: Clone + Eq + Ord + Debug + codec::Codec> IdentifierT for T {}

/// Aggregator trait for a PerThing that can be multiplied by u128 (ExtendedBalance).
pub trait PerThing128: PerThing + Mul<ExtendedBalance, Output = ExtendedBalance> {}
impl<T: PerThing + Mul<ExtendedBalance, Output = ExtendedBalance>> PerThing128 for T {}
