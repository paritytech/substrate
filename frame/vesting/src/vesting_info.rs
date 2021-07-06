// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Module to enforce private fields on `VestingInfo`.

use super::*;
use codec::MaxEncodedLen;

/// Struct to encode the vesting schedule of an individual account.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, MaxEncodedLen)]
pub struct VestingInfo<Balance, BlockNumber> {
	/// Locked amount at genesis.
	locked: Balance,
	/// Amount that gets unlocked every block after `starting_block`.
	per_block: Balance,
	/// Starting block for unlocking(vesting).
	starting_block: BlockNumber,
}

impl<Balance, BlockNumber> VestingInfo<Balance, BlockNumber>
where
	Balance: AtLeast32BitUnsigned + Copy,
	BlockNumber: AtLeast32BitUnsigned + Copy + Bounded,
{
	/// Instantiate a new `VestingInfo`.
	pub fn new<T: Config>(
		locked: Balance,
		per_block: Balance,
		starting_block: BlockNumber,
	) -> VestingInfo<Balance, BlockNumber> {
		VestingInfo { locked, per_block, starting_block }
	}

	/// Validate parameters for `VestingInfo`. Note that this does not check
	/// against `MinVestedTransfer` or the current block.
	pub fn validate<BlockNumberToBalance: Convert<BlockNumber, Balance>, T: Config>(
		&self,
	) -> Result<(), Error<T>> {
		ensure!(!self.locked.is_zero(), Error::<T>::InvalidScheduleParams);

		let max_block = BlockNumberToBalance::convert(BlockNumber::max_value());
		match self.locked.checked_div(&self.per_block) {
			None => return Err(Error::<T>::InfiniteSchedule), // `per_block` is 0
			Some(duration) => ensure!(duration < max_block, Error::<T>::InfiniteSchedule),
		};

		Ok(())
	}

	/// Potentially correct the `per_block` of a schedule. Typically called after `validate`.
	pub fn correct(mut self) -> Self {
		self.per_block = if self.per_block > self.locked { self.locked } else { self.per_block };
		self
	}

	/// Locked amount at schedule creation.
	pub fn locked(&self) -> Balance {
		self.locked
	}

	/// Amount that gets unlocked every block after `starting_block`.
	pub fn per_block(&self) -> Balance {
		self.per_block
	}

	/// Starting block for unlocking(vesting).
	pub fn starting_block(&self) -> BlockNumber {
		self.starting_block
	}

	/// Amount locked at block `n`.
	pub fn locked_at<BlockNumberToBalance: Convert<BlockNumber, Balance>>(
		&self,
		n: BlockNumber,
	) -> Balance {
		// Number of blocks that count toward vesting
		// Saturating to 0 when n < starting_block
		let vested_block_count = n.saturating_sub(self.starting_block);
		let vested_block_count = BlockNumberToBalance::convert(vested_block_count);
		// Return amount that is still locked in vesting
		vested_block_count
			.checked_mul(&self.per_block)
			.map(|to_unlock| self.locked.saturating_sub(to_unlock))
			.unwrap_or(Zero::zero())
	}

	/// Block number at which the schedule ends (as type `Balance`).
	pub fn ending_block_as_balance<BlockNumberToBalance: Convert<BlockNumber, Balance>, T: Config>(
		&self,
	) -> Result<Balance, DispatchError> {
		let starting_block = BlockNumberToBalance::convert(self.starting_block);
		let duration = if self.per_block >= self.locked {
			// If `per_block` is bigger than `locked`, the schedule will end
			// the block after starting.
			One::one()
		} else if self.per_block.is_zero() {
			// Check for div by 0 errors, which should only be from legacy
			// vesting schedules since new ones are validated for this.
			return Err(Error::<T>::InfiniteSchedule.into());
		} else {
			self.locked / self.per_block +
				if (self.locked % self.per_block).is_zero() {
					Zero::zero()
				} else {
					// `per_block` does not perfectly divide `locked`, so we need an extra block to
					// unlock some amount less than per_block
					One::one()
				}
		};

		Ok(starting_block.saturating_add(duration))
	}
}
