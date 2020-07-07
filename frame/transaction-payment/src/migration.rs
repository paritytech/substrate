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

//! Migration code to update storage.

use super::*;
use frame_support::storage::migration::take_storage_value;
use frame_support::weights::Weight;
use sp_runtime::FixedI64;

type OldMultiplier = FixedI64;

pub fn on_runtime_upgrade<T: Trait>() -> Weight {
	rename_and_convert::<T>()
}

// Change the storage name used by this pallet from `Balances` to `TransactionPayment`.
//
// Since the format of the storage items themselves have not changed, we do not
// need to keep track of a storage version. If the runtime does not need to be
// upgraded, nothing here will happen anyway.
//
// TODO: Also the type of the multiplier has changed in the mean-time we might want to 
// introduce a storage version?
fn rename_and_convert<T: Trait>() -> Weight {
	sp_runtime::print("🕊️  Migrating Transaction Payment.");

	let mut reads = 0;
	let mut writes = 0;
	if let Some(next_fee_multiplier) =
		take_storage_value::<OldMultiplier>(b"Balances", b"NextFeeMultiplier", &[])
	{
		let raw_multiplier = next_fee_multiplier.into_inner() as u128;
		// Fixed64 used 10^9 precision, where Fixed128 uses 10^18, so we need to add 9 zeros.
		let new_raw_multiplier = raw_multiplier.saturating_mul(1_000_000_000);
		let new_multiplier = Multiplier::from_inner(new_raw_multiplier);
		NextFeeMultiplier::put(new_multiplier);
		writes += 2;
	}
	reads += 1;

	sp_runtime::print("🕊️  Done Transaction Payment.");
	T::DbWeight::get().reads_writes(reads, writes)
}
