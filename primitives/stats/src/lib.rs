// Copyright 2017-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Usage statistics for Subtrate.
//! Structure used for storing the state backend statistics:
//! Number or reads, writes, cache reads, memory usage.

#![cfg_attr(not(feature = "std"), no_std)]
mod usage_info;
mod state_machine_stats;

pub use usage_info::{UsageInfo, UsageUnit};
pub use state_machine_stats::StateMachineStats;