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

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account};
use frame_support::traits::OnInitialize;

use crate::Module as Treasury;

const SEED: u32 = 0;

// Create the pre-requisite information needed to create a treasury `propose_spend`.
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

// Create the pre-requisite information needed to create a `report_awesome`.
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

// Create the pre-requisite information needed to call `tip_new`.
fn setup_tip<T: Trait>(r: u32, t: u32) ->
	Result<(T::AccountId, Vec<u8>, T::AccountId, BalanceOf<T>), &'static str>
{
	let tippers_count = T::Tippers::count();

	for i in 0 .. t {
		let member = account("member", i, SEED);
		T::Tippers::add(&member);
		ensure!(T::Tippers::contains(&member), "failed to add tipper");
	}

	ensure!(T::Tippers::count() == tippers_count + t as usize, "problem creating tippers");
	let caller = account("member", t - 1, SEED);
	let reason = vec![0; r as usize];
	let beneficiary = account("beneficiary", t, SEED);
	let value = T::Currency::minimum_balance().saturating_mul(100.into());
	Ok((caller, reason, beneficiary, value))
}

// Create `t` new tips for the tip proposal with `hash`.
// This function automatically makes the tip able to close.
fn create_tips<T: Trait>(t: u32, hash: T::Hash, value: BalanceOf<T>) -> Result<(), &'static str> {
	for i in 0 .. t {
		let caller = account("member", i, SEED);
		ensure!(T::Tippers::contains(&caller), "caller is not a tipper");
		Treasury::<T>::tip(RawOrigin::Signed(caller).into(), hash, value)?;
	}
	Tips::<T>::mutate(hash, |maybe_tip| {
		if let Some(open_tip) = maybe_tip {
			open_tip.closes = Some(T::BlockNumber::zero());
		}
	});
	Ok(())
}

// Create proposals that are approved for use in `on_initialize`.
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

const MAX_BYTES: u32 = 16384;
const MAX_TIPPERS: u32 = 100;

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
		let r in 0 .. MAX_BYTES;
		let (caller, reason, awesome_person) = setup_awesome::<T>(r);
	}: _(RawOrigin::Signed(caller), reason, awesome_person)

	retract_tip {
		let r in 0 .. MAX_BYTES;
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
		let r in 0 .. MAX_BYTES;
		let t in 1 .. MAX_TIPPERS;

		let (caller, reason, beneficiary, value) = setup_tip::<T>(r, t)?;
	}: _(RawOrigin::Signed(caller), reason, beneficiary, value)

	tip {
		let t in 1 .. MAX_TIPPERS;
		let (member, reason, beneficiary, value) = setup_tip::<T>(0, t)?;
		let value = T::Currency::minimum_balance().saturating_mul(100.into());
		Treasury::<T>::tip_new(
			RawOrigin::Signed(member).into(),
			reason.clone(),
			beneficiary.clone(),
			value
		)?;
		let reason_hash = T::Hashing::hash(&reason[..]);
		let hash = T::Hashing::hash_of(&(&reason_hash, &beneficiary));
		ensure!(Tips::<T>::contains_key(hash), "tip does not exist");
		create_tips::<T>(t - 1, hash.clone(), value)?;
		let caller = account("member", t - 1, SEED);
	}: _(RawOrigin::Signed(caller), hash, value)

	close_tip {
		let t in 1 .. MAX_TIPPERS;

		// Make sure pot is funded
		let pot_account = Treasury::<T>::account_id();
		let value = T::Currency::minimum_balance().saturating_mul(1_000_000_000.into());
		let _ = T::Currency::make_free_balance_be(&pot_account, value);

		// Set up a new tip proposal
		let (member, reason, beneficiary, value) = setup_tip::<T>(0, t)?;
		let value = T::Currency::minimum_balance().saturating_mul(100.into());
		Treasury::<T>::tip_new(
			RawOrigin::Signed(member).into(),
			reason.clone(),
			beneficiary.clone(),
			value
		)?;

		// Create a bunch of tips
		let reason_hash = T::Hashing::hash(&reason[..]);
		let hash = T::Hashing::hash_of(&(&reason_hash, &beneficiary));
		ensure!(Tips::<T>::contains_key(hash), "tip does not exist");
		create_tips::<T>(t, hash.clone(), value)?;

		let caller = account("caller", t, SEED);
	}: _(RawOrigin::Signed(caller), hash)

	on_initialize {
		let p in 0 .. 100;
		let pot_account = Treasury::<T>::account_id();
		let value = T::Currency::minimum_balance().saturating_mul(1_000_000_000.into());
		let _ = T::Currency::make_free_balance_be(&pot_account, value);
		create_approved_proposals::<T>(p)?;
	}: {
		Treasury::<T>::on_initialize(T::BlockNumber::zero());
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_propose_spend::<Test>());
			assert_ok!(test_benchmark_reject_proposal::<Test>());
			assert_ok!(test_benchmark_approve_proposal::<Test>());
			assert_ok!(test_benchmark_report_awesome::<Test>());
			assert_ok!(test_benchmark_retract_tip::<Test>());
			assert_ok!(test_benchmark_tip_new::<Test>());
			assert_ok!(test_benchmark_tip::<Test>());
			assert_ok!(test_benchmark_close_tip::<Test>());
			assert_ok!(test_benchmark_on_initialize::<Test>());
		});
	}
}
