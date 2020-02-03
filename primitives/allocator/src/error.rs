// Copyright 2020 Parity Technologies (UK) Ltd.
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

/// The error type used by the allocators.
#[derive(sp_core::RuntimeDebug)]
#[cfg_attr(feature = "std", derive(derive_more::Display))]
pub enum Error {
	/// Someone tried to allocate more memory than the allowed maximum per allocation.
	#[cfg_attr(feature = "std", display(fmt="Requested allocation size is too large"))]
	RequestedAllocationTooLarge,
	/// Allocator run out of space.
	#[cfg_attr(feature = "std", display(fmt="Allocator ran out of space"))]
	AllocatorOutOfSpace,
	/// Some other error occurred.
	Other(&'static str)
}

#[cfg(feature = "std")]
impl std::error::Error for Error {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		match self {
			_ => None,
		}
	}
}
