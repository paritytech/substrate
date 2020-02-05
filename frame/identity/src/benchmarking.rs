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
use sp_runtime::{BenchmarkResults, BenchmarkParameter};
use sp_runtime::traits::{Bounded, Benchmarking};

use crate::Module as Identity;

pub fn account<T: Trait>(index: u32) -> T::AccountId {
	let entropy = (b"benchmark", index).using_encoded(blake2_256);
	T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
}

trait BenchmarkingSetup<T> where
	T: Trait,
{
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)>;

	fn instance(&self, components: &[(BenchmarkParameter, u32)]) -> (crate::Call<T>, RawOrigin<T::AccountId>);

}

struct SetIdentity;
impl<T: Trait> BenchmarkingSetup<T> for SetIdentity {

	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// Registrar Count
			(BenchmarkParameter::R, 1, 16),
			// Additional Field Count
			(BenchmarkParameter::X, 1, 20)
		]
	}

	/// Assumes externalities are set up with a mutable state.
	///
	/// Panics if `component_name` isn't from `set_identity::components` or `component_value` is out of
	/// the range of `set_identity::components`.
	///
	/// Sets up state randomly and returns a randomly generated `set_identity` with sensible (fixed)
	/// values for all complexity components except those mentioned in the identity.
	fn instance(&self, components: &[(BenchmarkParameter, u32)]) -> (crate::Call<T>, RawOrigin<T::AccountId>)
	{
		// Add r registrars
		let r = components.iter().find(|&c| c.0 == BenchmarkParameter::R).unwrap();
		for i in 0..r.1 {
			let _ = T::Currency::make_free_balance_be(&account::<T>(i), BalanceOf::<T>::max_value());
			assert_eq!(Identity::<T>::add_registrar(RawOrigin::Root.into(), account::<T>(i)), Ok(()));
			assert_eq!(Identity::<T>::set_fee(RawOrigin::Signed(account::<T>(i)).into(), i.into(), 10.into()), Ok(()));
			let fields = IdentityFields(IdentityField::Display | IdentityField::Legal);
			assert_eq!(Identity::<T>::set_fields(RawOrigin::Signed(account::<T>(i)).into(), i.into(), fields), Ok(()));
		}

		sp_std::if_std!{
			println!("# Registrars {:?}", Registrars::<T>::get().len());
		}
		
		// Create identity info with x additional fields
		let x = components.iter().find(|&c| c.0 == BenchmarkParameter::X).unwrap();
		// 32 byte data that we reuse below
		let data = Data::Raw(vec![0; 32]);
		let info = IdentityInfo {
			additional: vec![(data.clone(), data.clone()); x.1 as usize],
			display: data.clone(),
			legal: data.clone(),
			web: data.clone(),
			riot: data.clone(),
			email: data.clone(),
			pgp_fingerprint: Some([0; 20]),
			image: data.clone(),
			twitter: data.clone(),
		};

		let caller = account::<T>(r.1 + 1);
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		// Return the `set_identity` call
		(crate::Call::<T>::set_identity(info), RawOrigin::Signed(caller))
	}
}

struct AddRegistrar;
impl<T: Trait> BenchmarkingSetup<T> for AddRegistrar {

	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// Registrar Count
			(BenchmarkParameter::R, 1, 16),
		]
	}

	/// Assumes externalities are set up with a mutable state.
	///
	/// Panics if `component_name` isn't from `set_identity::components` or `component_value` is out of
	/// the range of `set_identity::components`.
	///
	/// Sets up state randomly and returns a randomly generated `set_identity` with sensible (fixed)
	/// values for all complexity components except those mentioned in the identity.
	fn instance(&self, components: &[(BenchmarkParameter, u32)]) -> (crate::Call<T>, RawOrigin<T::AccountId>)
	{
		// Add r registrars
		let r = components.iter().find(|&c| c.0 == BenchmarkParameter::R).unwrap();
		for i in 0..r.1 {
			sp_std::if_std!{
				println!("Components {:?} Index {:?}", components, i);
			}
			let _ = T::Currency::make_free_balance_be(&account::<T>(i), BalanceOf::<T>::max_value());
			assert_eq!(Identity::<T>::add_registrar(RawOrigin::Root.into(), account::<T>(i)), Ok(()));
			sp_std::if_std!{
				println!("# Registrars {:?}", Registrars::<T>::get().len());
			}
		}
		// Return the `add_registrar` r + 1 call
		(crate::Call::<T>::add_registrar(account::<T>(r.1 + 1)), RawOrigin::Root)
	}
}

enum SelectedBenchmark {
	SetIdentity,
	AddRegistrar,
}

impl<T: Trait> BenchmarkingSetup<T> for SelectedBenchmark {
	fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)>
	{
		match self {
			Self::SetIdentity => <SetIdentity as BenchmarkingSetup<T>>::components(&SetIdentity),
			Self::AddRegistrar => <AddRegistrar as BenchmarkingSetup<T>>::components(&AddRegistrar),
		}
	}

	fn instance(&self, components: &[(BenchmarkParameter, u32)]) -> (crate::Call<T>, RawOrigin<T::AccountId>)
	{
		match self {
			Self::SetIdentity => <SetIdentity as BenchmarkingSetup<T>>::instance(&SetIdentity, components),
			Self::AddRegistrar => <AddRegistrar as BenchmarkingSetup<T>>::instance(&AddRegistrar, components),
		}
	}
}

impl<T: Trait> Benchmarking<BenchmarkResults> for Module<T> {
	const STEPS: u32 = 10;
	const REPEATS: u32 = 100;

	fn run_benchmarks(input: Vec<u8>) -> Vec<BenchmarkResults> {

		let selected_benchmark = match input.as_slice() {
			b"set_identity" => SelectedBenchmark::SetIdentity,
			b"add_registrar" => SelectedBenchmark::AddRegistrar,
			_ => return Vec::new(),
		};

		// first one is set_identity.		
		let components = <SelectedBenchmark as BenchmarkingSetup<T>>::components(&selected_benchmark);
		// results go here
		let mut results: Vec<BenchmarkResults> = Vec::new();
		// Select the component we will be benchmarking. Each component will be benchmarked.
		for (name, low, high) in components.iter() {
			// Create up to `STEPS` steps for that component between high and low.
			let step_size = ((high - low) / Self::STEPS).max(1);
			let num_of_steps = (high - low) / step_size;
			for s in 0..num_of_steps {
				// This is the value we will be testing for component `name`
				let component_value = low + step_size * s;

				// Select the mid value for all the other components.
				let c: Vec<(BenchmarkParameter, u32)> = components.iter()
					.map(|(n, l, h)|
						(*n, if n == name { component_value } else { (h - l) / 2 + l })
					).collect();

				for r in 0..Self::REPEATS {
					sp_std::if_std!{
						println!("STEP {:?} REPEAT {:?}", s, r);
					}
					let (call, caller) = <SelectedBenchmark as BenchmarkingSetup<T>>::instance(&selected_benchmark, &c);
					sp_io::benchmarking::commit_db();
					let start = sp_io::benchmarking::current_time();
					assert_eq!(call.dispatch(caller.into()), Ok(()));
					let finish = sp_io::benchmarking::current_time();
					let elapsed = finish - start;
					sp_io::benchmarking::wipe_db();
					results.push((c.clone(), elapsed));
				}
			}
		}
		return results;
	}
}

sp_api::decl_runtime_apis! {
	pub trait IdentityBenchmarks
	{
		fn run_benchmarks(input: Vec<u8>) -> Vec<BenchmarkResults>;
	}
}
