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
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

//! A crate that hosts a common definitions that are relevant for the pallet-contracts.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;

/// A result type of a get storage call.
pub type GetStorageResult = Result<Option<Vec<u8>>, ContractAccessError>;

/// The possible errors that can happen querying the storage of a contract.
#[derive(Eq, PartialEq, codec::Encode, codec::Decode, sp_runtime::RuntimeDebug)]
pub enum ContractAccessError {
	/// The given address doesn't point to a contract.
	DoesntExist,
	/// The specified contract is a tombstone and thus cannot have any storage.
	IsTombstone,
}

/// A result type of a `rent_projection` call.
pub type RentProjectionResult<BlockNumber> =
	Result<RentProjection<BlockNumber>, ContractAccessError>;

#[derive(Eq, PartialEq, codec::Encode, codec::Decode, sp_runtime::RuntimeDebug)]
pub enum RentProjection<BlockNumber> {
	/// Eviction is projected to happen at the specified block number.
	EvictionAt(BlockNumber),
	/// No eviction is scheduled.
	///
	/// E.g. because the contract accumulated enough funds to offset the rent storage costs.
	NoEviction,
}
