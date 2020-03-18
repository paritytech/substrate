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
use frame_support::storage::StorageValue;
use frame_benchmarking::{benchmarks, account};
use sp_runtime::traits::OnFinalize;

use crate::Module as Treasury;

const SEED: u32 = 0;

fn setup_proposal<T: Trait>(u: u32) -> (
	T::AccountId,
	BalanceOf<T>,
	<T::Lookup as StaticLookup>::Source,
) {
	let caller = account("caller", u, SEED);
	let value: BalanceOf<T> = T::ProposalBondMinimum::get().saturating_mul(100.into());
	let _ = T::Currency::make_free_balance_be(&caller, value);
	let beneficiary = account("beneficiary", u, SEED);
	let beneficiary_lookup = T::Lookup::unlookup(beneficiary);
	(caller, value, beneficiary_lookup)
}

fn setup_awesome<T: Trait>(length: u32) -> (T::AccountId, Vec<u8>, T::AccountId) {
	let caller = account("caller", 0, SEED);
	let value = T::TipReportDepositBase::get()
		+ T::TipReportDepositPerByte::get() * length.into()
		+ T::Currency::minimum_balance();
	let _ = T::Currency::make_free_balance_be(&caller, value);
	let reason = vec![0; length as usize];
	let awesome_person = account("awesome", 0, SEED);
	(caller, reason, awesome_person)
}

fn create_approved_proposals<T: Trait>(n: u32) -> Result<(), &'static str> {
	for i in 0 .. n {
		let (caller, value, lookup) = setup_proposal::<T>(i);
		Treasury::<T>::propose_spend(
			RawOrigin::Signed(caller).into(),
			value,
			lookup
		)?;
		let proposal_id = ProposalCount::get() - 1;
		Treasury::<T>::approve_proposal(RawOrigin::Root.into(), proposal_id)?;
	}
	ensure!(Approvals::get().len() == n as usize, "Not all approved");
	Ok(())
}

benchmarks! {
	_ { }

	propose_spend {
		let u in 0 .. 1000;
		let (caller, value, beneficiary_lookup) = setup_proposal::<T>(u);
	}: _(RawOrigin::Signed(caller), value, beneficiary_lookup)

	reject_proposal {
		let u in 0 .. 1000;
		let (caller, value, beneficiary_lookup) = setup_proposal::<T>(u);
		Treasury::<T>::propose_spend(
			RawOrigin::Signed(caller).into(),
			value,
			beneficiary_lookup
		)?;
		let proposal_id = ProposalCount::get() - 1;
	}: _(RawOrigin::Root, proposal_id)

	approve_proposal {
		let u in 0 .. 1000;
		let (caller, value, beneficiary_lookup) = setup_proposal::<T>(u);
		Treasury::<T>::propose_spend(
			RawOrigin::Signed(caller).into(),
			value,
			beneficiary_lookup
		)?;
		let proposal_id = ProposalCount::get() - 1;
	}: _(RawOrigin::Root, proposal_id)

	report_awesome {
		let r in 0 .. 16384;
		let (caller, reason, awesome_person) = setup_awesome::<T>(r);
	}: _(RawOrigin::Signed(caller), reason, awesome_person)

	retract_tip {
		let r in 0 .. 16384;
		let (caller, reason, awesome_person) = setup_awesome::<T>(r);
		Treasury::<T>::report_awesome(
			RawOrigin::Signed(caller.clone()).into(),
			reason.clone(),
			awesome_person.clone()
		)?;
		let reason_hash = T::Hashing::hash(&reason[..]);
		let hash = T::Hashing::hash_of(&(&reason_hash, &awesome_person));
	}: _(RawOrigin::Signed(caller), hash)

	tip_new {
		let r in 0 .. 16384;
		let t in 0 .. 100 => {
			let member = account("member", 0, SEED);
			T::Tippers::add(&member);
		};
		let caller = account("member", t, SEED);
		let reason = vec![0; r as usize];
		let beneficiary = account("beneficiary", t, SEED);
		let value = T::Currency::minimum_balance().saturating_mul(100.into());
	}: _(RawOrigin::Signed(caller), reason, beneficiary, value)

	// tip {

	// }

	// close_tip

	on_finalize {
		let p in 0 .. 100;
		let pot_account = Treasury::<T>::account_id();
		let value = T::Currency::minimum_balance().saturating_mul(1_000_000_000.into());
		let _ = T::Currency::make_free_balance_be(&pot_account, value);
		create_approved_proposals::<T>(p)?;
	}: {
		Treasury::<T>::on_finalize(T::BlockNumber::zero());
	}
}
