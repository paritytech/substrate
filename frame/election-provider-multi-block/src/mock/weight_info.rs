// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

// TODO: would love to ditch this, too big to handle here.

use crate::{self as multi_block};
use frame_support::dispatch::Weight;
use sp_runtime::traits::Zero;

frame_support::parameter_types! {
	pub static MockWeightInfo: bool = false;
}

pub struct DualMockWeightInfo;
impl multi_block::weights::WeightInfo for DualMockWeightInfo {
	fn on_initialize_nothing() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::on_initialize_nothing()
		}
	}
	fn on_initialize_open_signed() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::on_initialize_open_signed()
		}
	}
	fn on_initialize_open_unsigned_with_snapshot() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::on_initialize_open_unsigned_with_snapshot()
		}
	}
	fn on_initialize_open_unsigned_without_snapshot() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::on_initialize_open_unsigned_without_snapshot()
		}
	}
	fn finalize_signed_phase_accept_solution() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::finalize_signed_phase_accept_solution()
		}
	}
	fn finalize_signed_phase_reject_solution() -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::finalize_signed_phase_reject_solution()
		}
	}
	fn submit(c: u32) -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::submit(c)
		}
	}
	fn elect_queued(v: u32, t: u32, a: u32, d: u32) -> Weight {
		if MockWeightInfo::get() {
			Zero::zero()
		} else {
			<() as multi_block::weights::WeightInfo>::elect_queued(v, t, a, d)
		}
	}
	fn submit_unsigned(v: u32, t: u32, a: u32, d: u32) -> Weight {
		if MockWeightInfo::get() {
			// 10 base
			// 5 per edge.
			(10 as Weight).saturating_add((5 as Weight).saturating_mul(a as Weight))
		} else {
			<() as multi_block::weights::WeightInfo>::submit_unsigned(v, t, a, d)
		}
	}
	fn feasibility_check(v: u32, t: u32, a: u32, d: u32) -> Weight {
		if MockWeightInfo::get() {
			// 10 base
			// 5 per edge.
			(10 as Weight).saturating_add((5 as Weight).saturating_mul(a as Weight))
		} else {
			<() as multi_block::weights::WeightInfo>::feasibility_check(v, t, a, d)
		}
	}
}
