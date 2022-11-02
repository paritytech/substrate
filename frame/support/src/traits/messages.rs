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

//! Traits for managing message queuing and handling.

use codec::{Decode, Encode, FullCodec, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_core::Get;
use sp_runtime::{BoundedSlice, RuntimeDebug};
use sp_std::{fmt::Debug, prelude::*};
use sp_weights::Weight;

#[derive(Copy, Clone, Eq, PartialEq, Encode, Decode, TypeInfo, RuntimeDebug)]
pub enum ProcessMessageError {
	/// The message data format is unknown (e.g. unrecognised header)
	BadFormat,
	/// The message data is bad (e.g. decoding returns an error).
	Corrupt,
	/// The message format is unsupported (e.g. old XCM version).
	Unsupported,
	/// Message processing was not attempted because it was not certain that the weight limit
	/// would be respected. The parameter gives the maximum weight which the message could take
	/// to process.
	Overweight(Weight),
}

pub trait ProcessMessage {
	/// The transport from where a message originates.
	type Origin: FullCodec + MaxEncodedLen + Clone + Eq + PartialEq + TypeInfo + Debug;

	/// Process the given message, using no more than `weight_limit` in weight to do so.
	fn process_message(
		message: &[u8],
		origin: Self::Origin,
		weight_limit: Weight,
	) -> Result<(bool, Weight), ProcessMessageError>;
}

pub trait ServiceQueues {
	/// Service all message queues in some fair manner.
	///
	/// - `weight_limit`: The maximum amount of dynamic weight that this call can use.
	///
	/// Returns the dynamic weight used by this call; is never greater than `weight_limit`.
	fn service_queues(weight_limit: Weight) -> Weight;
}

pub trait EnqueueMessage<Origin: MaxEncodedLen> {
	type MaxMessageLen: Get<u32>;

	/// Enqueue a single `message` from a specific `origin`.
	///
	/// Infallible.
	fn enqueue_message(message: BoundedSlice<u8, Self::MaxMessageLen>, origin: Origin);

	/// Enqueue multiple `messages` from a specific `origin`.
	///
	/// If no `message.len()` is greater than `HEAP_SIZE - Origin::max_encoded_len()`, then this
	/// is guaranteed to succeed. In the case of `Err`, no messages are queued.
	fn enqueue_messages<'a>(
		messages: impl Iterator<Item = BoundedSlice<'a, u8, Self::MaxMessageLen>>,
		origin: Origin,
	);
}
