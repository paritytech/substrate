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
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Primitives for slots-based consensus engines.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_timestamp::Timestamp;

/// Unit type wrapper that represents a slot.
#[derive(Debug, Encode, MaxEncodedLen, Decode, Eq, Clone, Copy, Default, Ord, TypeInfo)]
#[cfg_attr(feature = "std", derive(serde::Serialize, serde::Deserialize))]
pub struct Slot(u64);

impl core::ops::Deref for Slot {
	type Target = u64;

	fn deref(&self) -> &u64 {
		&self.0
	}
}

impl core::ops::Add for Slot {
	type Output = Self;

	fn add(self, other: Self) -> Self {
		Self(self.0 + other.0)
	}
}

impl core::ops::Add<u64> for Slot {
	type Output = Self;

	fn add(self, other: u64) -> Self {
		Self(self.0 + other)
	}
}

impl<T: Into<u64> + Copy> core::cmp::PartialEq<T> for Slot {
	fn eq(&self, eq: &T) -> bool {
		self.0 == (*eq).into()
	}
}

impl<T: Into<u64> + Copy> core::cmp::PartialOrd<T> for Slot {
	fn partial_cmp(&self, other: &T) -> Option<core::cmp::Ordering> {
		self.0.partial_cmp(&(*other).into())
	}
}

impl Slot {
	/// Create a new slot by calculating it from the given timestamp and slot duration.
	pub const fn from_timestamp(timestamp: Timestamp, slot_duration: SlotDuration) -> Self {
		Slot(timestamp.as_millis() / slot_duration.as_millis())
	}

	/// Saturating addition.
	pub fn saturating_add<T: Into<u64>>(self, rhs: T) -> Self {
		Self(self.0.saturating_add(rhs.into()))
	}

	/// Saturating subtraction.
	pub fn saturating_sub<T: Into<u64>>(self, rhs: T) -> Self {
		Self(self.0.saturating_sub(rhs.into()))
	}
}

#[cfg(feature = "std")]
impl std::fmt::Display for Slot {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.0)
	}
}

impl From<u64> for Slot {
	fn from(slot: u64) -> Slot {
		Slot(slot)
	}
}

impl From<Slot> for u64 {
	fn from(slot: Slot) -> u64 {
		slot.0
	}
}

/// A slot duration defined in milliseconds.
#[derive(Clone, Copy, Debug, Encode, Decode, Hash, PartialOrd, Ord, PartialEq, Eq, TypeInfo)]
pub struct SlotDuration(u64);

impl SlotDuration {
	/// Initialize from the given milliseconds.
	pub const fn from_millis(millis: u64) -> Self {
		Self(millis)
	}
}

impl SlotDuration {
	/// Returns `self` as a `u64` representing the duration in milliseconds.
	pub const fn as_millis(&self) -> u64 {
		self.0
	}
}

#[cfg(feature = "std")]
impl SlotDuration {
	/// Returns `self` as [`sp_std::time::Duration`].
	pub const fn as_duration(&self) -> sp_std::time::Duration {
		sp_std::time::Duration::from_millis(self.0)
	}
}

/// Represents an equivocation proof. An equivocation happens when a validator
/// produces more than one block on the same slot. The proof of equivocation
/// are the given distinct headers that were signed by the validator and which
/// include the slot number.
#[derive(Clone, Debug, Decode, Encode, PartialEq, TypeInfo)]
pub struct EquivocationProof<Header, Id> {
	/// Returns the authority id of the equivocator.
	pub offender: Id,
	/// The slot at which the equivocation happened.
	pub slot: Slot,
	/// The first header involved in the equivocation.
	pub first_header: Header,
	/// The second header involved in the equivocation.
	pub second_header: Header,
}
