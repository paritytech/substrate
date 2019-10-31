// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Linear historical data.

#[cfg(not(feature = "std"))]
use rstd::{vec::Vec, vec};
use crate::HistoricalValue;


/// Array like buffer for in memory storage.
/// By in memory we expect that this will
/// not required persistence and is not serialized.
#[cfg(not(feature = "std"))]
pub(crate) type InMemory<V, I> = Vec<HistoricalValue<V, I>>;

/// Array like buffer for in memory storage.
/// By in memory we expect that this will
/// not required persistence and is not serialized.
#[cfg(feature = "std")]
pub(crate) type InMemory<V, I> = smallvec::SmallVec<[HistoricalValue<V, I>; ALLOCATED_HISTORY]>;

/// Size of preallocated history per element.
/// Currently at two for committed and prospective only.
/// It means that using transaction in a module got a direct allocation cost.
#[cfg(feature = "std")]
const ALLOCATED_HISTORY: usize = 2;
