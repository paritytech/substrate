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

//! Treasury pallet benchmarking.

use super::*;

use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account};
use sp_runtime::traits::SaturatedConversion;

use crate::Module as Treasury;

const SEED: u32 = 0;


benchmarks! {
	_ { }

	propose_spend {
		let u in 0 .. 1000;
		let caller = account("caller", u, SEED);
		let value: BalanceOf<T> = T::ProposalBondMinimum::get().saturating_mul(100.into());
		let _ = T::Currency::make_free_balance_be(&caller, value);
		let beneficiary = account("beneficiary", u, SEED);
		let beneficiary_lookup = T::Lookup::unlookup(beneficiary);
	}: _(RawOrigin::Signed(caller), value, beneficiary_lookup)

	reject_proposal {
		let u in 0 .. 1000;
		let reject_origin = T::RejectOrigin;
		let value: BalanceOf<T> = T::ProposalBondMinimum::get().saturating_mul(100.into());
		let _ = T::Currency::make_free_balance_be(&caller, value);
		let beneficiary = account("beneficiary", u, SEED);
		let beneficiary_lookup = T::Lookup::unlookup(beneficiary);
	}: _(RawOrigin::Signed(caller), value, beneficiary_lookup)
}
