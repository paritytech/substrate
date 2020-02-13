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

//! Identity pallet benchmarking.

use super::*;

use frame_system::RawOrigin;
use sp_io::hashing::blake2_256;
use sp_runtime::{BenchmarkResults, BenchmarkParameter, selected_benchmark};
use sp_runtime::traits::{Bounded, Benchmarking, BenchmarkingSetup, Dispatchable};

use crate::Module as Identity;

// The maximum number of identity registrars we will test.
const MAX_REGISTRARS: u32 = 50;

// Support Functions
fn account<T: Trait>(name: &'static str, index: u32) -> T::AccountId {
	let entropy = (name, index).using_encoded(blake2_256);
	T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
}

// Adds `r` registrars to the Identity Pallet. These registrars will have set fees and fields.
fn add_registrars<T: Trait>(r: u32) -> Result<(), &'static str> {
	for i in 0..r {
		let _ = T::Currency::make_free_balance_be(&account::<T>("registrar", i), BalanceOf::<T>::max_value());
		Identity::<T>::add_registrar(RawOrigin::Root.into(), account::<T>("registrar", i))?;
		Identity::<T>::set_fee(RawOrigin::Signed(account::<T>("registrar", i)).into(), i.into(), 10.into())?;
		let fields = IdentityFields(
			IdentityField::Display | IdentityField::Legal | IdentityField::Web | IdentityField::Riot
			| IdentityField::Email | IdentityField::PgpFingerprint | IdentityField::Image | IdentityField::Twitter
		);
		Identity::<T>::set_fields(RawOrigin::Signed(account::<T>("registrar", i)).into(), i.into(), fields)?;
	}

	assert_eq!(Registrars::<T>::get().len(), r as usize);
	Ok(())
}

// Adds `s` sub-accounts to the identity of `who`. Each wil have 32 bytes of raw data added to it.
// This additionally returns the vector of sub-accounts to it can be modified if needed.
fn add_sub_accounts<T: Trait>(who: T::AccountId, s: u32) -> Result<Vec<(T::AccountId, Data)>, &'static str> {
	let mut subs = Vec::new();
	let who_origin = RawOrigin::Signed(who.clone());
	let data = Data::Raw(vec![0; 32]);

	for i in 0..s {
		let sub_account = account::<T>("sub", i);
		subs.push((sub_account, data.clone()));
	}
	Identity::<T>::set_subs(who_origin.into(), subs.clone())?;

	return Ok(subs)
}

// This creates an `IdentityInfo` object with `num_fields` extra fields.
// All data is pre-populated with some arbitrary bytes.
fn create_identity_info<T: Trait>(num_fields: u32) -> IdentityInfo {
	let data = Data::Raw(vec![0; 32]);

	let info = IdentityInfo {
		additional: vec![(data.clone(), data.clone()); num_fields as usize],
		display: data.clone(),
		legal: data.clone(),
		web: data.clone(),
		riot: data.clone(),
		email: data.clone(),
		pgp_fingerprint: Some([0; 20]),
		image: data.clone(),
		twitter: data.clone(),
	};

	return info
}

macro_rules! benchmark {
	( $item:ident { $( $rest:tt )* }: $dispatch:ident ( $origin:expr $( , $arg:expr )* ) ) => {
		benchmark_backend! {
			$item , $dispatch {} ( $origin $( , $arg )* ) { $( $rest )* }
		}
	}
}

macro_rules! benchmark_backend {
	// parsing arms
	($item:ident , $dispatch:ident { $( PRE { $( $parsed:tt )* } )* } ( $origin:expr $( , $arg:expr )* ) {
		let $pre_id:tt : $pre_ty:ty = $pre_ex:expr;
		$( $rest:tt )*
	}) => {
		benchmark_backend! {
			$item , $dispatch {
				$( PRE { $( $parsed )* } )*
				PRE { $pre_id , $pre_ty , $pre_ex }
			} ( $origin $( , $arg )* ) { $( $rest )* }
		}
	};
	($item:ident , $dispatch:ident { $( $parsed:tt )* } ( $origin:expr $( , $arg:expr )* ) {
		let $param_var:ident as $param:ident in $param_from:tt .. $param_to:expr => $param_instancer:expr;
		$( $rest:tt )*
	}) => {
		benchmark_backend! {
			$item , $dispatch {
				$( $parsed )*
				PARAM { $param_var , $param , $param_from , $param_to , $param_instancer }
			} ( $origin $( , $arg )* ) { $( $rest )* }
		}
	};
	// mutation arm to look after the default tail of `=> ()`
	($item:ident , $dispatch:ident { $( $parsed:tt )* } ( $origin:expr $( , $arg:expr )* ) {
		let $param_var:ident as $param:ident in $param_from:tt .. $param_to:expr;
		$( $rest:tt )*
	}) => {
		benchmark_backend! {
			$item , $dispatch { $( $parsed )* } ( $origin $( , $arg )* ) {
				let $param_var as $param in $param_from .. $param_to => ();
				$( $rest )*
			}
		}
	};
	// mutation arm to look after `let _ =`
	($item:ident , $dispatch:ident { $( $parsed:tt )* } ( $origin:expr $( , $arg:expr )* ) {
		let $pre_id:tt = $pre_ex:expr;
		$( $rest:tt )*
	}) => {
		benchmark_backend! {
			$item , $dispatch { $( $parsed )* } ( $origin $( , $arg )* ) {
				let $pre_id : _ = $pre_ex;
				$( $rest )*
			}
		}
	};
	// actioning arm
	($item:ident , $dispatch:ident {
		$( PRE { $pre_id:tt , $pre_ty:ty , $pre_ex:expr } )*
		$( PARAM { $param_var:ident , $param:ident , $param_from:tt , $param_to:expr , $param_instancer:expr } )*
	} ( $origin:expr $( , $arg:expr )* ) { $( $post:tt )* } ) => {
		struct $item;
		impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for $item {
			fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
				vec![
					// Registrar Count
					$(
						(BenchmarkParameter::$param, $param_from, $param_to)
					),*
				]
			}

			fn instance(&self, components: &[(BenchmarkParameter, u32)])
				-> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
			{
				$(
					// Prepare instance
					let $param_var = components.iter().find(|&c| c.0 == BenchmarkParameter::$param).unwrap().1;
				)*
				$( let $pre_id : $pre_ty = $pre_ex; )*
				$(
					// Prepare instance
					$param_instancer;
				)*
				$( $post )*

				// Return the `add_registrar` r + 1 call
				Ok((crate::Call::<T>::$dispatch($($arg),*), $origin))
			}
		}
	}
}

// Benchmark `add_registrar` extrinsic.
benchmark! {
	AddRegistrar {
		let r as R in 1 .. MAX_REGISTRARS => benchmarking::add_registrars::<T>(r)?;
	}: add_registrar(RawOrigin::Root, account::<T>("registrar", r + 1))
}

// Benchmark `add_registrar` extrinsic.
benchmark! {
	SetIdentity {
		let r as R in 1 .. MAX_REGISTRARS => benchmarking::add_registrars::<T>(r)?;
		let x as X in 1 .. T::MaxAdditionalFields::get();
		let caller = {
			// The target user
			let caller = account::<T>("caller", r);
			let caller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(caller.clone());
			let caller_origin: <T as frame_system::Trait>::Origin = RawOrigin::Signed(caller.clone()).into();
			let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

			// Add an initial identity
			let initial_info = benchmarking::create_identity_info::<T>(1);
			Identity::<T>::set_identity(caller_origin.clone(), initial_info)?;

			// User requests judgement from all the registrars, and they approve
			for i in 0..r {
				Identity::<T>::request_judgement(caller_origin.clone(), i, 10.into())?;
				Identity::<T>::provide_judgement(
					RawOrigin::Signed(account::<T>("registrar", i)).into(),
					i,
					caller_lookup.clone(),
					Judgement::Reasonable
				)?;
			}
			caller
		};
	}: set_identity(
		RawOrigin::Signed(caller),
		benchmarking::create_identity_info::<T>(x)
	)
}

benchmark! {
	SetSubs {
		let s as S in 1 .. T::MaxSubAccounts::get();
		let caller = account::<T>("caller", 0);
		let caller_origin: <T as frame_system::Trait>::Origin = RawOrigin::Signed(caller.clone()).into();
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		// Create their main identity
		let info = benchmarking::create_identity_info::<T>(1);
		Identity::<T>::set_identity(caller_origin.clone(), info)?;
	}: set_subs(RawOrigin::Signed(caller), {
		let mut subs = add_sub_accounts::<T>(caller.clone(), s)?;
		// Generic data to be used.
		let data = Data::Raw(vec![0; 32]);
		// Create an s+1 sub account to add
		subs.push((account::<T>("sub", s + 1), data));
		subs
	})
}

benchmark! {
	ClearIdentity {
		let caller = account::<T>("caller", 0);
		let caller_origin = <T as frame_system::Trait>::Origin::from(RawOrigin::Signed(caller.clone()));
		let caller_lookup = <T::Lookup as StaticLookup>::unlookup(caller.clone());
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		let r as R in 1 .. MAX_REGISTRARS => benchmarking::add_registrars::<T>(r)?;
		let s as S in 1 .. T::MaxSubAccounts::get() => {
			// Give them s many sub accounts
			let _ = benchmarking::add_sub_accounts::<T>(caller.clone(), s)?;
		};
		let x as X in 1 .. T::MaxAdditionalFields::get() => {
			// Create their main identity with x additional fields
			let info = benchmarking::create_identity_info::<T>(x);
			Identity::<T>::set_identity(caller_origin.clone(), info)?;
		};
		// User requests judgement from all the registrars, and they approve
		for i in 0..r {
			Identity::<T>::request_judgement(caller_origin.clone(), i, 10.into())?;
			Identity::<T>::provide_judgement(
				RawOrigin::Signed(account::<T>("registrar", i)).into(),
				i,
				caller_lookup.clone(),
				Judgement::Reasonable
			)?;
		}
	}: clear_identity(RawOrigin::Signed(caller))
}

benchmark! {
	RequestJudgement {
		let caller = account::<T>("caller", 0);
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		let r as R in 1 .. MAX_REGISTRARS => benchmarking::add_registrars::<T>(r)?;
		let x as X in 1 .. T::MaxAdditionalFields::get() => {
			// Create their main identity with x additional fields
			let info = benchmarking::create_identity_info::<T>(x);
			let caller_origin = <T as frame_system::Trait>::Origin::from(RawOrigin::Signed(caller.clone()));
			Identity::<T>::set_identity(caller_origin, info)?;
		};
	}: request_judgement(RawOrigin::Signed(caller), r - 1, 10.into())
}

benchmark! {
	CancelRequest {
		let caller = account::<T>("caller", 0);
		let caller_origin = <T as frame_system::Trait>::Origin::from(RawOrigin::Signed(caller.clone()));
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		let r as R in 1 .. MAX_REGISTRARS => benchmarking::add_registrars::<T>(r)?;
		let x as X in 1 .. T::MaxAdditionalFields::get() => {
			// Create their main identity with x additional fields
			let info = benchmarking::create_identity_info::<T>(x);
			Identity::<T>::set_identity(caller_origin.clone(), info)?;
		};
		Identity::<T>::request_judgement(caller_origin, r - 1, 10.into())?;
	}: cancel_request(RawOrigin::Signed(caller), r - 1)
}

benchmark! {
	SetFee {
		let caller = account::<T>("caller", 0);
		let r as R in 1 .. MAX_REGISTRARS => benchmarking::add_registrars::<T>(r)?;
		Identity::<T>::add_registrar(RawOrigin::Root.into(), caller.clone())?;
	}: set_fee(RawOrigin::Signed(caller), r, 10.into())
}

benchmark! {
	SetAccountId {
		let caller = account::<T>("caller", 0);
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		let r as R in 1 .. MAX_REGISTRARS => benchmarking::add_registrars::<T>(r)?;
		Identity::<T>::add_registrar(RawOrigin::Root.into(), caller.clone())?;
	}: set_account_id(RawOrigin::Signed(caller), r, account::<T>("new", 0))
}

benchmark! {
	SetFields {
		let caller = account::<T>("caller", 0);
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		let r as R in 1 .. MAX_REGISTRARS => benchmarking::add_registrars::<T>(r)?;
		Identity::<T>::add_registrar(RawOrigin::Root.into(), caller.clone())?;
		let fields = IdentityFields(
			IdentityField::Display | IdentityField::Legal | IdentityField::Web | IdentityField::Riot
			| IdentityField::Email | IdentityField::PgpFingerprint | IdentityField::Image | IdentityField::Twitter
		);
	}: set_fields(RawOrigin::Signed(caller), r, fields)
}

benchmark! {
	ProvideJudgement {
		// The user
		let user = account::<T>("user", r);
		let user_origin = <T as frame_system::Trait>::Origin::from(RawOrigin::Signed(user.clone()));
		let user_lookup = <T::Lookup as StaticLookup>::unlookup(user.clone());
		let _ = T::Currency::make_free_balance_be(&user, BalanceOf::<T>::max_value());

		let caller = account::<T>("caller", r);
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r as R in 1 .. MAX_REGISTRARS => benchmarking::add_registrars::<T>(r)?;
		let x as X in 1 .. T::MaxAdditionalFields::get() => {
			let info = benchmarking::create_identity_info::<T>(x);
			Identity::<T>::set_identity(user_origin.clone(), info)?;
		};

		Identity::<T>::add_registrar(RawOrigin::Root.into(), caller.clone())?;
		Identity::<T>::request_judgement(user_origin.clone(), r, 10.into())?;
	}: provide_judgement(RawOrigin::Signed(caller), r, user_lookup, Judgement::Reasonable)
}

benchmark! {
	KillIdentity {
		let caller = account::<T>("caller", 0);
		let caller_origin: <T as frame_system::Trait>::Origin = RawOrigin::Signed(caller.clone()).into();
		let caller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(caller.clone());
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r as R in 1 .. MAX_REGISTRARS => benchmarking::add_registrars::<T>(r)?;
		let s as S in 1 .. T::MaxSubAccounts::get() => {
			// Give them s many sub accounts
			let _ = benchmarking::add_sub_accounts::<T>(caller.clone(), s)?;
		};
		let x as X in 1 .. T::MaxAdditionalFields::get() => {
			// Create their main identity with x additional fields
			let info = benchmarking::create_identity_info::<T>(x);
			Identity::<T>::set_identity(caller_origin.clone(), info)?;
		};

		// User requests judgement from all the registrars, and they approve
		for i in 0..r {
			Identity::<T>::request_judgement(caller_origin.clone(), i, 10.into())?;
			Identity::<T>::provide_judgement(
				RawOrigin::Signed(account::<T>("registrar", i)).into(),
				i,
				caller_lookup.clone(),
				Judgement::Reasonable
			)?;
		}
	}: kill_identity(RawOrigin::Root, caller_lookup)
}

// The list of available benchmarks for this pallet.
selected_benchmark!(
	AddRegistrar,
	SetIdentity,
	SetSubs,
	ClearIdentity,
	RequestJudgement,
	CancelRequest,
	SetFee,
	SetAccountId,
	SetFields,
	ProvideJudgement,
	KillIdentity
);

impl<T: Trait> Benchmarking<BenchmarkResults> for Module<T> {
	fn run_benchmark(extrinsic: Vec<u8>, steps: u32, repeat: u32) -> Result<Vec<BenchmarkResults>, &'static str> {
		// Map the input to the selected benchmark.
		let selected_benchmark = match extrinsic.as_slice() {
			b"add_registrar" => SelectedBenchmark::AddRegistrar,
			b"set_identity" => SelectedBenchmark::SetIdentity,
			b"set_subs" => SelectedBenchmark::SetSubs,
			b"clear_identity" => SelectedBenchmark::ClearIdentity,
			b"request_judgement" => SelectedBenchmark::RequestJudgement,
			b"cancel_request" => SelectedBenchmark::CancelRequest,
			b"set_fee" => SelectedBenchmark::SetFee,
			b"set_account_id" => SelectedBenchmark::SetAccountId,
			b"set_fields" => SelectedBenchmark::SetFields,
			b"provide_judgement" => SelectedBenchmark::ProvideJudgement,
			b"kill_identity" => SelectedBenchmark::KillIdentity,
			_ => return Err("Could not find extrinsic."),
		};

		// Warm up the DB
		sp_io::benchmarking::commit_db();
		sp_io::benchmarking::wipe_db();

		// first one is set_identity.
		let components = <SelectedBenchmark as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::components(&selected_benchmark);
		// results go here
		let mut results: Vec<BenchmarkResults> = Vec::new();
		// Select the component we will be benchmarking. Each component will be benchmarked.
		for (name, low, high) in components.iter() {
			// Create up to `STEPS` steps for that component between high and low.
			let step_size = ((high - low) / steps).max(1);
			let num_of_steps = (high - low) / step_size;
			for s in 0..num_of_steps {
				// This is the value we will be testing for component `name`
				let component_value = low + step_size * s;

				// Select the mid value for all the other components.
				let c: Vec<(BenchmarkParameter, u32)> = components.iter()
					.map(|(n, l, h)|
						(*n, if n == name { component_value } else { (h - l) / 2 + l })
					).collect();

				// Run the benchmark `repeat` times.
				for _ in 0..repeat {
					// Set up the externalities environment for the setup we want to benchmark.
					let (call, caller) = <SelectedBenchmark as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::instance(&selected_benchmark, &c)?;
					// Commit the externalities to the database, flushing the DB cache.
					// This will enable worst case scenario for reading from the database.
					sp_io::benchmarking::commit_db();
					// Run the benchmark.
					let start = sp_io::benchmarking::current_time();
					call.dispatch(caller.into())?;
					let finish = sp_io::benchmarking::current_time();
					let elapsed = finish - start;
					results.push((c.clone(), elapsed));
					// Wipe the DB back to the genesis state.
					sp_io::benchmarking::wipe_db();
				}
			}
		}
		return Ok(results);
	}
}
