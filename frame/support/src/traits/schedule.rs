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

//! Traits and associated utilities for scheduling dispatchables in FRAME.

use codec::{Codec, Decode, Encode, EncodeLike, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_runtime::{traits::Saturating, DispatchError, RuntimeDebug};
use sp_std::{fmt::Debug, prelude::*, result::Result};

/// Information relating to the period of a scheduled task. First item is the length of the
/// period and the second is the number of times it should be executed in total before the task
/// is considered finished and removed.
pub type Period<BlockNumber> = (BlockNumber, u32);

/// Priority with which a call is scheduled. It's just a linear amount with lowest values meaning
/// higher priority.
pub type Priority = u8;

/// The dispatch time of a scheduled task.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub enum DispatchTime<BlockNumber> {
	/// At specified block.
	At(BlockNumber),
	/// After specified number of blocks.
	After(BlockNumber),
}

impl<BlockNumber: Saturating + Copy> DispatchTime<BlockNumber> {
	pub fn evaluate(&self, since: BlockNumber) -> BlockNumber {
		match &self {
			Self::At(m) => *m,
			Self::After(m) => m.saturating_add(since),
		}
	}
}

/// The highest priority. We invert the value so that normal sorting will place the highest
/// priority at the beginning of the list.
pub const HIGHEST_PRIORITY: Priority = 0;
/// Anything of this value or lower will definitely be scheduled on the block that they ask for,
/// even if it breaches the `MaximumWeight` limitation.
pub const HARD_DEADLINE: Priority = 63;
/// The lowest priority. Most stuff should be around here.
pub const LOWEST_PRIORITY: Priority = 255;

/// Type representing an encodable value or the hash of the encoding of such a value.
#[derive(Clone, Eq, PartialEq, Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub enum MaybeHashed<T, Hash> {
	/// The value itself.
	Value(T),
	/// The hash of the encoded value which this value represents.
	Hash(Hash),
}

impl<T, H> From<T> for MaybeHashed<T, H> {
	fn from(t: T) -> Self {
		MaybeHashed::Value(t)
	}
}

/// Error type for `MaybeHashed::lookup`.
#[derive(Clone, Eq, PartialEq, Encode, Decode, RuntimeDebug, TypeInfo, MaxEncodedLen)]
pub enum LookupError {
	/// A call of this hash was not known.
	Unknown,
	/// The preimage for this hash was known but could not be decoded into a `Call`.
	BadFormat,
}

impl<T: Decode, H> MaybeHashed<T, H> {
	pub fn as_value(&self) -> Option<&T> {
		match &self {
			Self::Value(c) => Some(c),
			Self::Hash(_) => None,
		}
	}

	pub fn as_hash(&self) -> Option<&H> {
		match &self {
			Self::Value(_) => None,
			Self::Hash(h) => Some(h),
		}
	}

	pub fn ensure_requested<P: PreimageProvider<H>>(&self) {
		match &self {
			Self::Value(_) => (),
			Self::Hash(hash) => P::request_preimage(hash),
		}
	}

	pub fn ensure_unrequested<P: PreimageProvider<H>>(&self) {
		match &self {
			Self::Value(_) => (),
			Self::Hash(hash) => P::unrequest_preimage(hash),
		}
	}

	pub fn resolved<P: PreimageProvider<H>>(self) -> (Self, Option<H>) {
		match self {
			Self::Value(c) => (Self::Value(c), None),
			Self::Hash(h) => {
				let data = match P::get_preimage(&h) {
					Some(p) => p,
					None => return (Self::Hash(h), None),
				};
				match T::decode(&mut &data[..]) {
					Ok(c) => (Self::Value(c), Some(h)),
					Err(_) => (Self::Hash(h), None),
				}
			},
		}
	}
}

pub mod v1 {
	use super::*;

	/// A type that can be used as a scheduler.
	pub trait Anon<BlockNumber, Call, Origin> {
		/// An address which can be used for removing a scheduled task.
		type Address: Codec + Clone + Eq + EncodeLike + Debug + TypeInfo;

		/// Schedule a dispatch to happen at the beginning of some block in the future.
		///
		/// This is not named.
		fn schedule(
			when: DispatchTime<BlockNumber>,
			maybe_periodic: Option<Period<BlockNumber>>,
			priority: Priority,
			origin: Origin,
			call: Call,
		) -> Result<Self::Address, DispatchError>;

		/// Cancel a scheduled task. If periodic, then it will cancel all further instances of that,
		/// also.
		///
		/// Will return an error if the `address` is invalid.
		///
		/// NOTE: This guaranteed to work only *before* the point that it is due to be executed.
		/// If it ends up being delayed beyond the point of execution, then it cannot be cancelled.
		///
		/// NOTE2: This will not work to cancel periodic tasks after their initial execution. For
		/// that, you must name the task explicitly using the `Named` trait.
		fn cancel(address: Self::Address) -> Result<(), ()>;

		/// Reschedule a task. For one-off tasks, this dispatch is guaranteed to succeed
		/// only if it is executed *before* the currently scheduled block. For periodic tasks,
		/// this dispatch is guaranteed to succeed only before the *initial* execution; for
		/// others, use `reschedule_named`.
		///
		/// Will return an error if the `address` is invalid.
		fn reschedule(
			address: Self::Address,
			when: DispatchTime<BlockNumber>,
		) -> Result<Self::Address, DispatchError>;

		/// Return the next dispatch time for a given task.
		///
		/// Will return an error if the `address` is invalid.
		fn next_dispatch_time(address: Self::Address) -> Result<BlockNumber, ()>;
	}

	/// A type that can be used as a scheduler.
	pub trait Named<BlockNumber, Call, Origin> {
		/// An address which can be used for removing a scheduled task.
		type Address: Codec + Clone + Eq + EncodeLike + sp_std::fmt::Debug;

		/// Schedule a dispatch to happen at the beginning of some block in the future.
		///
		/// - `id`: The identity of the task. This must be unique and will return an error if not.
		fn schedule_named(
			id: Vec<u8>,
			when: DispatchTime<BlockNumber>,
			maybe_periodic: Option<Period<BlockNumber>>,
			priority: Priority,
			origin: Origin,
			call: Call,
		) -> Result<Self::Address, ()>;

		/// Cancel a scheduled, named task. If periodic, then it will cancel all further instances
		/// of that, also.
		///
		/// Will return an error if the `id` is invalid.
		///
		/// NOTE: This guaranteed to work only *before* the point that it is due to be executed.
		/// If it ends up being delayed beyond the point of execution, then it cannot be cancelled.
		fn cancel_named(id: Vec<u8>) -> Result<(), ()>;

		/// Reschedule a task. For one-off tasks, this dispatch is guaranteed to succeed
		/// only if it is executed *before* the currently scheduled block.
		fn reschedule_named(
			id: Vec<u8>,
			when: DispatchTime<BlockNumber>,
		) -> Result<Self::Address, DispatchError>;

		/// Return the next dispatch time for a given task.
		///
		/// Will return an error if the `id` is invalid.
		fn next_dispatch_time(id: Vec<u8>) -> Result<BlockNumber, ()>;
	}

	impl<T, BlockNumber, Call, Origin> Anon<BlockNumber, Call, Origin> for T
	where
		T: v2::Anon<BlockNumber, Call, Origin>,
	{
		type Address = T::Address;

		fn schedule(
			when: DispatchTime<BlockNumber>,
			maybe_periodic: Option<Period<BlockNumber>>,
			priority: Priority,
			origin: Origin,
			call: Call,
		) -> Result<Self::Address, DispatchError> {
			let c = MaybeHashed::<Call, T::Hash>::Value(call);
			T::schedule(when, maybe_periodic, priority, origin, c)
		}

		fn cancel(address: Self::Address) -> Result<(), ()> {
			T::cancel(address)
		}

		fn reschedule(
			address: Self::Address,
			when: DispatchTime<BlockNumber>,
		) -> Result<Self::Address, DispatchError> {
			T::reschedule(address, when)
		}

		fn next_dispatch_time(address: Self::Address) -> Result<BlockNumber, ()> {
			T::next_dispatch_time(address)
		}
	}

	impl<T, BlockNumber, Call, Origin> Named<BlockNumber, Call, Origin> for T
	where
		T: v2::Named<BlockNumber, Call, Origin>,
	{
		type Address = T::Address;

		fn schedule_named(
			id: Vec<u8>,
			when: DispatchTime<BlockNumber>,
			maybe_periodic: Option<Period<BlockNumber>>,
			priority: Priority,
			origin: Origin,
			call: Call,
		) -> Result<Self::Address, ()> {
			let c = MaybeHashed::<Call, T::Hash>::Value(call);
			T::schedule_named(id, when, maybe_periodic, priority, origin, c)
		}

		fn cancel_named(id: Vec<u8>) -> Result<(), ()> {
			T::cancel_named(id)
		}

		fn reschedule_named(
			id: Vec<u8>,
			when: DispatchTime<BlockNumber>,
		) -> Result<Self::Address, DispatchError> {
			T::reschedule_named(id, when)
		}

		fn next_dispatch_time(id: Vec<u8>) -> Result<BlockNumber, ()> {
			T::next_dispatch_time(id)
		}
	}
}

pub mod v2 {
	use super::*;

	/// A type that can be used as a scheduler.
	pub trait Anon<BlockNumber, Call, Origin> {
		/// An address which can be used for removing a scheduled task.
		type Address: Codec + Clone + Eq + EncodeLike + Debug + TypeInfo;
		/// A means of expressing a call by the hash of its encoded data.
		type Hash;

		/// Schedule a dispatch to happen at the beginning of some block in the future.
		///
		/// This is not named.
		fn schedule(
			when: DispatchTime<BlockNumber>,
			maybe_periodic: Option<Period<BlockNumber>>,
			priority: Priority,
			origin: Origin,
			call: MaybeHashed<Call, Self::Hash>,
		) -> Result<Self::Address, DispatchError>;

		/// Cancel a scheduled task. If periodic, then it will cancel all further instances of that,
		/// also.
		///
		/// Will return an error if the `address` is invalid.
		///
		/// NOTE: This guaranteed to work only *before* the point that it is due to be executed.
		/// If it ends up being delayed beyond the point of execution, then it cannot be cancelled.
		///
		/// NOTE2: This will not work to cancel periodic tasks after their initial execution. For
		/// that, you must name the task explicitly using the `Named` trait.
		fn cancel(address: Self::Address) -> Result<(), ()>;

		/// Reschedule a task. For one-off tasks, this dispatch is guaranteed to succeed
		/// only if it is executed *before* the currently scheduled block. For periodic tasks,
		/// this dispatch is guaranteed to succeed only before the *initial* execution; for
		/// others, use `reschedule_named`.
		///
		/// Will return an error if the `address` is invalid.
		fn reschedule(
			address: Self::Address,
			when: DispatchTime<BlockNumber>,
		) -> Result<Self::Address, DispatchError>;

		/// Return the next dispatch time for a given task.
		///
		/// Will return an error if the `address` is invalid.
		fn next_dispatch_time(address: Self::Address) -> Result<BlockNumber, ()>;
	}

	/// A type that can be used as a scheduler.
	pub trait Named<BlockNumber, Call, Origin> {
		/// An address which can be used for removing a scheduled task.
		type Address: Codec + Clone + Eq + EncodeLike + sp_std::fmt::Debug;
		/// A means of expressing a call by the hash of its encoded data.
		type Hash;

		/// Schedule a dispatch to happen at the beginning of some block in the future.
		///
		/// - `id`: The identity of the task. This must be unique and will return an error if not.
		fn schedule_named(
			id: Vec<u8>,
			when: DispatchTime<BlockNumber>,
			maybe_periodic: Option<Period<BlockNumber>>,
			priority: Priority,
			origin: Origin,
			call: MaybeHashed<Call, Self::Hash>,
		) -> Result<Self::Address, ()>;

		/// Cancel a scheduled, named task. If periodic, then it will cancel all further instances
		/// of that, also.
		///
		/// Will return an error if the `id` is invalid.
		///
		/// NOTE: This guaranteed to work only *before* the point that it is due to be executed.
		/// If it ends up being delayed beyond the point of execution, then it cannot be cancelled.
		fn cancel_named(id: Vec<u8>) -> Result<(), ()>;

		/// Reschedule a task. For one-off tasks, this dispatch is guaranteed to succeed
		/// only if it is executed *before* the currently scheduled block.
		fn reschedule_named(
			id: Vec<u8>,
			when: DispatchTime<BlockNumber>,
		) -> Result<Self::Address, DispatchError>;

		/// Return the next dispatch time for a given task.
		///
		/// Will return an error if the `id` is invalid.
		fn next_dispatch_time(id: Vec<u8>) -> Result<BlockNumber, ()>;
	}
}

pub use v1::*;

use super::PreimageProvider;
