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

//! The unsigned phase implementation.

use crate::two_phase::*;
use codec::Encode;
use sp_arithmetic::traits::SaturatedConversion;
use sp_npos_elections::is_score_better;
use sp_runtime::Perbill;

impl<T: Trait> Module<T> where ExtendedBalance: From<InnerOf<CompactAccuracyOf<T>>> {}

#[cfg(test)]
mod tests {
	use super::{mock::*, *};
}
