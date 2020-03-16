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
use frame_support::storage::migration::{put_storage_value, take_storage_value};

pub fn on_runtime_upgrade() {
	change_name_balances_to_transaction_payment()
}

// Change the storage name used by this pallet from `Balances` to `TransactionPayment`.
//
// Since the format of the storage items themselves have not changed, we do not
// need to keep track of a storage version. If the runtime does not need to be
// upgraded, nothing here will happen anyway.

fn change_name_balances_to_transaction_payment() {
	sp_runtime::print("Migrating Transaction Payment.");

	if let Some(next_fee_multiplier) = take_storage_value::<Multiplier>(b"Balances", b"NextFeeMultiplier", &[]) {
		put_storage_value(b"TransactionPayment", b"NextFeeMultiplier", &[], next_fee_multiplier);
	}
}
