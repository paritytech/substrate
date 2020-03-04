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
use frame_support::{
	decl_module, decl_event, decl_storage, ensure, decl_error,
	traits::{Currency, ReservableCurrency, OnUnbalanced, Get, BalanceStatus},
	weights::SimpleDispatchInfo,
};
use sp_runtime::traits::Bounded;

use crate::Module as Utility;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

// Support Functions
fn account<T: Trait>(name: &'static str, index: u32) -> T::AccountId {
    let entropy = index.using_encoded(blake2_256);
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
        let t in 2 .. 64 => { t };
    }

    batch {
        let n in ...;
        let i in _ .. _ => ();
        let a in _ .. _ => ();
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
        let t in ...;

        // TODO verify this utilizes the heaviest path in ApproveAsMulti

        // the only valid path is in case the number of signatories matches the threshold
        // even too many will error
        let threshold : u16 = t.try_into().unwrap();      
        let signatories_count : u32 = threshold.try_into().unwrap();
        
        use sp_std;
        sp_std::if_std!{
            println!("must get {} of {} where there are {}", threshold, <T as Trait>::MaxSignatories::get(), signatories_count);
        }

        let mut other_signatories = (1u32..=signatories_count).into_iter()
            .map(|idx| account::<T>("Tester", idx))
            .take(signatories_count.try_into().unwrap())
            .collect::<Vec<_>>();
        
        other_signatories.push(account::<T>("Alfred J. Kwak", 9999));
        other_signatories.push(account::<T>("Peter Pan", 1981));
        
        // make sure all accounts have sufficient funds
        other_signatories.iter().for_each(|account| {
            let _ = T::Currency::make_free_balance_be(&account, BalanceOf::<T>::max_value());
        });

        // sort, because that is what's required by ApproveAsMulti's other_siganatories field
        other_signatories.sort();

        let author = other_signatories.pop().unwrap();
        let collective = other_signatories.pop().unwrap();

        let timepoint : Timepoint<T::BlockNumber> = Utility::<T>::timepoint();

        let call : <T as Trait>::Call = nop_call::<T>();

        // the reference to be used in the multisig call
        let call_hash = BlakeTwo256::hash_of(&call);
        let call_hash : [u8;32] = call_hash.as_ref().try_into().expect("Signature length mismatch");

        call.dispatch(RawOrigin::Signed(author).into())?;

    } : _(
        RawOrigin::Signed(collective),
        threshold,
        other_signatories,
        None, //Some(timepoint),
        call_hash
    )
}
