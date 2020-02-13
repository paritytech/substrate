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

//! Utility pallet benchmarking.

use super::*;

use codec::{Decode, Encode};
use frame_system::RawOrigin;
use frame_system;
use sp_io::hashing::blake2_256;
use sp_runtime::traits::{Benchmarking, BenchmarkingSetup, Bounded, Dispatchable, Hash, BlakeTwo256};
use sp_runtime::{BenchmarkParameter, BenchmarkResults};
use core::convert::TryInto;

use crate::Module as Utility;

// Support Functions
fn account<T: Trait>(name: &'static str, index: u32) -> T::AccountId {
    let entropy = (name, index).using_encoded(blake2_256);
    T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
}

fn nop_call<T: Trait>() -> <T as Trait>::Call where <T as Trait>::Call: core::convert::From<Call<T>> {
    crate::Call::<T>::batch(vec![]).into()
}

// Benchmark `batch` util extrinsic.
struct Batch;
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for Batch where <T as Trait>::Call : core::convert::From<crate::Call<T>> + Encode {
    fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
        vec![
            // number of elements in the vector to use
            (BenchmarkParameter::N, 1, 64),
        ]
    }

    fn instance(
        &self,
        components: &[(BenchmarkParameter, u32)],
    ) -> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str> {
        let n: usize  = components.iter()
            .find(|param| param.0 == BenchmarkParameter::N)
            .expect("Must contain param N")
            .1.try_into().unwrap();
        let calls: Vec<<T as Trait>::Call> = core::iter::repeat_with(|| {
                nop_call::<T>()
            } )
            .take(n)
            .collect::<Vec<_>>();

        Ok((crate::Call::<T>::batch(calls), RawOrigin::Signed(account::<T>("Bud Spencer", 1961)) ))
    }
}

// Benchmark `as_sub` util extrinsic.
struct AsSub;
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for AsSub where <T as Trait>::Call : core::convert::From<crate::Call<T>> + Encode {
    fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
        vec![
            // number of elements in the vector to use
            (BenchmarkParameter::A, 1, 32),
			(BenchmarkParameter::I, 1, 32),
        ]
    }

    fn instance(
        &self,
        components: &[(BenchmarkParameter, u32)],
    ) -> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str> {
        let a : usize = components.iter()
            .find(|param| param.0 == BenchmarkParameter::A)
            .expect("Must contain param A")
			.1.try_into().expect("u32 to usize must succeed");
		let index = components.iter()
            .find(|param| param.0 == BenchmarkParameter::I)
            .expect("Must contain param I")
            .1.try_into().expect("u32 to u16 must succeed");
        let call: Box<<T as Trait>::Call> = Box::new(
            nop_call::<T>()
        );
	Ok((crate::Call::<T>::as_sub(index, call), RawOrigin::Signed(account::<T>("Jackie Chan", 111)) ))
    }
}

// Benchmark `as_sub` util extrinsic.
struct ApproveAsMulti;
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for ApproveAsMulti where <T as Trait>::Call : core::convert::From<crate::Call<T>> + Encode {
    fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
        vec![
            // multisig number of signatures
            (BenchmarkParameter::S, 0, 64),
            // multisig number of signatures threshold, must be at least one
            (BenchmarkParameter::T, 1, 64),
            // TODO height
        ]
    }

    fn instance(
        &self,
        components: &[(BenchmarkParameter, u32)],
    ) -> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str> {

        let signatories_count : u32 = components.iter()
            .find(|param| param.0 == BenchmarkParameter::S)
            .expect("Must contain param S")
            .1.try_into().unwrap();
        let threshold : u16 = components.iter()
            .find(|param| param.0 == BenchmarkParameter::T)
            .expect("Must contain param T")
            .1.try_into().unwrap();

        let other_signatories = (1u32..=signatories_count).into_iter().map(|idx| account::<T>("Tester", idx))
            .take(signatories_count.try_into().unwrap())
            .collect::<Vec<_>>();

        let timepoint : Timepoint<T::BlockNumber> = Utility::<T>::timepoint();


        // TODO does this have to be made known before approve_as_multi can be used?
        let call : <T as Trait>::Call = nop_call::<T>();
        //let call_hash = <<T as frame_system::Trait>::Hashing>::hash_of(&call);
        let call_hash = BlakeTwo256::hash_of(&call);
        let call_hash : [u8;32] = call_hash.as_ref().try_into().expect("Signature length mismatch");

        call.dispatch(RawOrigin::Signed(account::<T>("Peter Pan", 1981)).into())?;

        Ok((
            crate::Call::<T>::approve_as_multi(
                threshold,
                other_signatories,
                Some(timepoint),
                call_hash,
            ),
            RawOrigin::Signed(account::<T>("Alfred J. Kwak", 9999)),
        ))
    }
}

// The list of available benchmarks for this pallet.
enum SelectedBenchmark {
    Batch,
    AsSub,
    ApproveAsMulti,
}

// Allow us to select a benchmark from the list of available benchmarks.
impl<T: Trait> BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for SelectedBenchmark  where <T as Trait>::Call : core::convert::From<crate::Call<T>> + Encode{
    fn components(&self) -> Vec<(BenchmarkParameter, u32, u32)> {
        match self {
            Self::Batch => {
                <Batch as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::components(
                    &Batch,
                )
            }
            Self::AsSub => {
                <AsSub as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::components(
                    &AsSub,
                )
            }
            Self::ApproveAsMulti => {
                <ApproveAsMulti as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::components(
                    &ApproveAsMulti,
                )
            }
        }
    }

    fn instance(
        &self,
        components: &[(BenchmarkParameter, u32)],
    ) -> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str> {
        match self {
            Self::Batch => {
                <Batch as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::instance(
                    &Batch, components,
                )
            }
            Self::AsSub => {
                <AsSub as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::instance(
                    &AsSub, components,
                )
            }
            Self::ApproveAsMulti => {
                <ApproveAsMulti as BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::instance(
                    &ApproveAsMulti, components,
                )
            }
        }
    }
}

impl<T: Trait> Benchmarking<BenchmarkResults> for Module<T> where <T as Trait>::Call : core::convert::From<crate::Call<T>> {
    fn run_benchmark(
        extrinsic: Vec<u8>,
        steps: u32,
        repeat: u32,
    ) -> Result<Vec<BenchmarkResults>, &'static str> {
        // Map the input to the selected benchmark.
        let selected_benchmark = match extrinsic.as_slice() {
            b"batch" => SelectedBenchmark::Batch,
            b"as_sub" => SelectedBenchmark::AsSub,
            b"approve_as_multi" => SelectedBenchmark::ApproveAsMulti,
            _ => return Err("Could not find extrinsic."),
        };

        // Warm up the DB
        sp_io::benchmarking::commit_db();
        sp_io::benchmarking::wipe_db();

        let components = <SelectedBenchmark as BenchmarkingSetup<
            T,
            crate::Call<T>,
            RawOrigin<T::AccountId>,
        >>::components(&selected_benchmark);
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
                let c: Vec<(BenchmarkParameter, u32)> = components
                    .iter()
                    .map(|(n, l, h)| {
                        (
                            *n,
                            if n == name {
                                component_value
                            } else {
                                (h - l) / 2 + l
                            },
                        )
                    })
                    .collect();

                // Run the benchmark `repeat` times.
                for _ in 0..repeat {
                    // Set up the externalities environment for the setup we want to benchmark.
                    let (call, caller) = <SelectedBenchmark as BenchmarkingSetup<
                        T,
                        crate::Call<T>,
                        RawOrigin<T::AccountId>,
                    >>::instance(&selected_benchmark, &c)?;
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
