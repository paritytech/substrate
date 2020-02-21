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
use frame_benchmarking::{
    BenchmarkResults, BenchmarkParameter, benchmarking, Benchmarking,
    BenchmarkingSetup,
};
use frame_benchmarking::benchmarks;
use sp_io::hashing::blake2_256;
use sp_runtime::traits::{Dispatchable, Hash, BlakeTwo256};
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

benchmarks! {
    _ {
        let n in 0 .. 64 => { n };
        let i in 0 .. 64 => { i };
        let a in 0 .. 64 => { a };
        let s in 0 .. 64 => { s };
        let t in 0 .. 64 => { t };
    }

    batch {
        let n in ...;
        let i in _ .. _ => ();
        let a in _ .. _ => ();
        let s in _ .. _ => ();
        let t in _ .. _ => ();


        let calls: Vec<<T as Trait>::Call> = core::iter::repeat_with(|| {
            nop_call::<T>()
        })
        .take(n as usize)
        .collect::<Vec<_>>();

    }: _(RawOrigin::Signed(account::<T>("Bud Spencer", 1961)), calls)


    as_sub {
        let n in _ .. _ => ();
        let i in ...;
        let a in ...;
        let s in _ .. _ => ();
        let t in _ .. _ => ();

        let idx : u16 = i.try_into().unwrap();

        let call: Box<<T as Trait>::Call> = Box::new(
            nop_call::<T>()
        );
    } : _( RawOrigin::Signed(account::<T>("Jackie Chan", 111)), idx, call)


    approve_as_multi {
        let n in _ .. _ => ();
        let i in _ .. _ => ();
        let a in _ .. _ => ();
        let s in ...;
        let t in ...;

        let signatories_count : u32 = s.try_into().unwrap();
        let other_signatories = (1u32..=signatories_count).into_iter().map(|idx| account::<T>("Tester", idx))
            .take(signatories_count.try_into().unwrap())
            .collect::<Vec<_>>();

        let threshold : u16 = t.try_into().unwrap();
        let timepoint : Timepoint<T::BlockNumber> = Utility::<T>::timepoint();

        let call : <T as Trait>::Call = nop_call::<T>();

        let call_hash = BlakeTwo256::hash_of(&call);
        let call_hash : [u8;32] = call_hash.as_ref().try_into().expect("Signature length mismatch");

        call.dispatch(RawOrigin::Signed(account::<T>("Peter Pan", 1981)).into())?;
    } : _(
        RawOrigin::Signed(account::<T>("Alfred J. Kwak", 9999)),
        threshold,
        other_signatories,
        Some(timepoint),
        call_hash
    )

}