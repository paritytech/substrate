// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use sp_runtime::{traits::{Convert}, Perbill};
use sp_npos_elections::ElectionScore;
use frame_support::traits::Get;

/// No verification for external solutions. Accept everything.
///
/// Should be sued with care; this may allow any solution to be accepted, as there are no 'absolute'
/// restrictions in place.
pub struct NoVerification;
impl Convert<ElectionScore, bool> for NoVerification {
	fn convert(_: ElectionScore) -> bool {
		true
	}
}

/// Ensures that any solution must have a higher score than `M`.
pub struct EnsureMinScore<M: Get<ElectionScore>>(sp_std::marker::PhantomData<M>);
impl<M: Get<ElectionScore>> Convert<ElectionScore, bool> for EnsureMinScore<M> {
	fn convert(s: ElectionScore) -> bool {
		let minimum = M::get();
		sp_npos_elections::is_score_better(s, minimum, Perbill::zero())
	}
}
