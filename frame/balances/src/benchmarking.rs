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

//! Balances pallet benchmarking.

use super::*;

use frame_system::RawOrigin;
use sp_io::hashing::blake2_256;
use sp_runtime::{BenchmarkResults, BenchmarkParameter, selected_benchmarks};
use sp_runtime::traits::{Bounded, BenchmarkingSetup, Dispatchable};

use crate::Module as Balances;

// Support Functions
fn account<T: Trait>(name: &'static str, index: u32) -> T::AccountId {
	let entropy = (name, index).using_encoded(blake2_256);
	T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
}

// Benchmark `transfer` extrinsic with the worst possible conditions:
// * Transfer will kill the sender account.
// * Transfer will create the recipient account.
struct Transfer;
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for Transfer {
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// Existential Deposit Multiplier
			(BenchmarkParameter::E, 2, 1000),
			// User Seed
			(BenchmarkParameter::U, 1, 1000),
		]
	}

	fn instance(&self, components: &[(BenchmarkParameter, u32)])
		-> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
		// Constants
		let ed = T::ExistentialDeposit::get();
		
		// Select an account
		let u = components.iter().find(|&c| c.0 == BenchmarkParameter::U).unwrap().1;
		let user = account::<T>("user", u);
		let user_origin = RawOrigin::Signed(user.clone());

		// Give some multiple of the existential deposit + creation fee + transfer fee
		let e = components.iter().find(|&c| c.0 == BenchmarkParameter::E).unwrap().1;
		let mut balance = ed.saturating_mul(e.into());
		balance += T::CreationFee::get();
		let _ = <Balances<T> as Currency<_>>::make_free_balance_be(&user, balance);

		// Transfer `e - 1` existential deposits + 1 unit, which guarantees to create one account, and reap this user.
		let recipient = account::<T>("recipient", u);
		let recipient_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(recipient);
		let transfer_amt = ed.saturating_mul((e - 1).into()) + 1.into();

		// Return the `transfer` call
		Ok((crate::Call::<T>::transfer(recipient_lookup, transfer_amt), user_origin))
	}
}

// Benchmark `transfer` with the best possible condition:
// * Both accounts exist and will continue to exist.
struct TransferBestCase;
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for TransferBestCase {
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// Existential Deposit Multiplier
			(BenchmarkParameter::E, 2, 1000),
			// User Seed
			(BenchmarkParameter::U, 1, 1000),
		]
	}

	fn instance(&self, components: &[(BenchmarkParameter, u32)])
		-> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
		// Constants
		let ed = T::ExistentialDeposit::get();
		
		// Select a sender
		let u = components.iter().find(|&c| c.0 == BenchmarkParameter::U).unwrap().1;
		let user = account::<T>("user", u);
		let user_origin = RawOrigin::Signed(user.clone());

		// Select a recipient
		let recipient = account::<T>("recipient", u);
		let recipient_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(recipient.clone());

		// Get the existential deposit multiplier
		let e = components.iter().find(|&c| c.0 == BenchmarkParameter::E).unwrap().1;

		// Give the sender account max funds for transfer (their account will never reasonably be killed).
		let _ = <Balances<T> as Currency<_>>::make_free_balance_be(&user, T::Balance::max_value());

		// Give the recipient account existential deposit (thus their account already exists).
		let _ = <Balances<T> as Currency<_>>::make_free_balance_be(&recipient, ed);

		// Transfer e * existential deposit.
		let transfer_amt = ed.saturating_mul(e.into());

		// Return the `transfer` call
		Ok((crate::Call::<T>::transfer(recipient_lookup, transfer_amt), user_origin))
	}
}

// Benchmark `transfer_keep_alive` with the worst possible condition:
// * The recipient account is created.
struct TransferKeepAlive;
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for TransferKeepAlive {
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// Existential Deposit Multiplier
			(BenchmarkParameter::E, 2, 1000),
			// User Seed
			(BenchmarkParameter::U, 1, 1000),
		]
	}

	fn instance(&self, components: &[(BenchmarkParameter, u32)])
		-> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
		// Constants
		let ed = T::ExistentialDeposit::get();
		
		// Select a sender
		let u = components.iter().find(|&c| c.0 == BenchmarkParameter::U).unwrap().1;
		let user = account::<T>("user", u);
		let user_origin = RawOrigin::Signed(user.clone());

		// Select a recipient
		let recipient = account::<T>("recipient", u);
		let recipient_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(recipient.clone());

		// Get the existential deposit multiplier
		let e = components.iter().find(|&c| c.0 == BenchmarkParameter::E).unwrap().1;

		// Give the sender account max funds, thus a transfer will not kill account.
		let _ = <Balances<T> as Currency<_>>::make_free_balance_be(&user, T::Balance::max_value());

		// Transfer e * existential deposit.
		let transfer_amt = ed.saturating_mul(e.into());

		// Return the `transfer_keep_alive` call
		Ok((crate::Call::<T>::transfer_keep_alive(recipient_lookup, transfer_amt), user_origin))
	}
}

// Benchmark `set_balance` coming from ROOT account. This always creates an account.
struct SetBalance;
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for SetBalance {
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// Existential Deposit Multiplier
			(BenchmarkParameter::E, 2, 1000),
			// User Seed
			(BenchmarkParameter::U, 1, 1000),
		]
	}

	fn instance(&self, components: &[(BenchmarkParameter, u32)])
		-> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
		// Constants
		let ed = T::ExistentialDeposit::get();
		
		// Select a sender
		let u = components.iter().find(|&c| c.0 == BenchmarkParameter::U).unwrap().1;
		let user = account::<T>("user", u);
		let user_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(user.clone());

		// Get the existential deposit multiplier for free and reserved
		let e = components.iter().find(|&c| c.0 == BenchmarkParameter::E).unwrap().1;
		let balance_amt = ed.saturating_mul(e.into());

		// Return the `set_balance` call
		Ok((crate::Call::<T>::set_balance(user_lookup, balance_amt, balance_amt), RawOrigin::Root))
	}
}

// Benchmark `set_balance` coming from ROOT account. This always kills an account.
struct SetBalanceKilling;
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for SetBalanceKilling {
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// Existential Deposit Multiplier
			(BenchmarkParameter::E, 2, 1000),
			// User Seed
			(BenchmarkParameter::U, 1, 1000),
		]
	}

	fn instance(&self, components: &[(BenchmarkParameter, u32)])
		-> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
	{
		// Constants
		let ed = T::ExistentialDeposit::get();
		
		// Select a sender
		let u = components.iter().find(|&c| c.0 == BenchmarkParameter::U).unwrap().1;
		let user = account::<T>("user", u);
		let user_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(user.clone());

		// Get the existential deposit multiplier for free and reserved
		let e = components.iter().find(|&c| c.0 == BenchmarkParameter::E).unwrap().1;
		// Give the user some initial balance
		let balance_amt = ed.saturating_mul(e.into());
		let _ = <Balances<T> as Currency<_>>::make_free_balance_be(&user, balance_amt);

		// Return the `set_balance` call that will kill the account
		Ok((crate::Call::<T>::set_balance(user_lookup, 0.into(), 0.into()), RawOrigin::Root))
	}
}

// The list of available benchmarks for this pallet.
selected_benchmarks!([
	Transfer,
	TransferBestCase,
	TransferKeepAlive,
	SetBalance,
	SetBalanceKilling
],
	|
		call: Call<T>,
		caller: RawOrigin<T::AccountId>,
		c: Vec<(BenchmarkParameter, u32)>,
		results: &mut Vec<BenchmarkResults>,
	| -> Result<(), &'static str> {
		sp_io::benchmarking::commit_db();
		// Run the benchmark.
		let start = sp_io::benchmarking::current_time();
		call.dispatch(caller.clone().into())?;
		let finish = sp_io::benchmarking::current_time();
		let elapsed = finish - start;
		sp_std::if_std!{
			if let RawOrigin::Signed(who) = caller.clone() {
				let balance = Account::<T>::get(&who).free;
				println!("Free Balance {:?}", balance);
			}
		}
		results.push((c.clone(), elapsed));
		// Wipe the DB back to the genesis state.
		sp_io::benchmarking::wipe_db();
		Ok(())
	}
);
