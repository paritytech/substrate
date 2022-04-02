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

//! Types used in the Name Service pallet.

use crate::*;
use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{traits::Currency, BoundedVec, RuntimeDebug};
use scale_info::TypeInfo;

// Allows easy access our Pallet's `Balance` and `NegativeImbalance` type.
//
// Comes from `Currency` interface.
pub type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
pub type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;

pub type CommitmentOf<T> = Commitment<
	<T as frame_system::Config>::AccountId,
	BalanceOf<T>,
	<T as frame_system::Config>::BlockNumber,
>;

pub type RegistrationOf<T> = Registration<
	<T as frame_system::Config>::AccountId,
	BalanceOf<T>,
	<T as frame_system::Config>::BlockNumber,
>;

pub type NameHash = [u8; 32];
pub type CommitmentHash = [u8; 32];

pub type BoundedNameOf<T> = BoundedVec<u8, <T as Config>::MaxNameLength>;
pub type BoundedTextOf<T> = BoundedVec<u8, <T as Config>::MaxTextLength>;

/// The commitment a user makes before registering the name.
#[derive(Encode, Decode, Default, MaxEncodedLen, TypeInfo, RuntimeDebug)]
pub struct Commitment<AccountId, Balance, BlockNumber> {
	/// Who will retain ownership of the claimed domain.
	///
	/// This can be different than the person who made the commitment (depositor).
	pub owner: AccountId,
	/// When the commitment was made.
	pub when: BlockNumber,
	/// The user placing a deposit to keep the commitment in storage.
	pub depositor: AccountId,
	/// The deposit amount.
	pub deposit: Balance,
}

/// The name registration information for any parent or subnode.
#[derive(Encode, Decode, Default, MaxEncodedLen, TypeInfo, RuntimeDebug)]
pub struct Registration<AccountId, Balance, BlockNumber> {
	/// The owner of a name registration. This user has full control over the name
	/// at all times.
	pub owner: AccountId,
	/// The controller of a name registration. They have access to update the resolver
	/// information and register new subdomains.
	pub controller: AccountId,
	/// The expiration date of a name registration, after which, the registration can be
	/// dissolved and reclaimed by someone else.
	pub expiry: Option<BlockNumber>,
	/// The deposit on hold for a name registration. This will always be reserved
	/// by the owner.
	pub deposit: Option<Balance>,
}

/// The an object used to store arbitrary bytes, and a corresponding deposit.
#[derive(Encode, Decode, Default, MaxEncodedLen, TypeInfo, RuntimeDebug)]
pub struct BytesStorage<AccountId, Balance, BoundedBytes> {
	pub bytes: BoundedBytes,
	pub depositor: AccountId,
	pub deposit: Balance,
}
