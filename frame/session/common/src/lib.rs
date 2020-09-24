// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

#![cfg_attr(not(feature = "std"), no_std)]

use sp_runtime::traits::{Member, Convert};
use frame_support::Parameter;

pub trait ValidatorIdentification<AccountId> {
	/// A stable ID for a validator.
	type ValidatorId: Member + Parameter;

	/// A conversion from account ID to validator ID.
	///
	/// Its cost must be at most one storage read.
	type ValidatorIdOf: Convert<AccountId, Option<Self::ValidatorId>>;

	/// Full identification of the validator.
	type FullIdentification: Parameter;

	/// A conversion from validator ID to full identification.
	///
	/// This should contain any references to economic actors associated with the
	/// validator, since they may be outdated by the time this is queried from a
	/// historical trie.
	///
	/// It must return the identification for the current session index.
	type FullIdentificationOf: Convert<Self::ValidatorId, Option<Self::FullIdentification>>;
}

/// A tuple of the validator's ID and their full identification.
pub type IdentificationTuple<AccountId, T> = (
	<T as ValidatorIdentification<AccountId>>::ValidatorId,
	<T as ValidatorIdentification<AccountId>>::FullIdentification
);
