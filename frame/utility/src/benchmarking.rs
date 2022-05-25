// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Benchmarks for Utility Pallet

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_benchmarking::{account, benchmarks, whitelisted_caller};
use frame_system::RawOrigin;
use sp_runtime::traits::Bounded;

const SEED: u32 = 0;

fn assert_last_event<T: Config>(generic_event: <T as Config>::Event) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

mod crypto {
	use codec::Decode;
	use sp_core::{crypto::AccountId32, ed25519};
	use sp_io::crypto::{ed25519_generate, ed25519_sign};
	use sp_runtime::{traits::IdentifyAccount, MultiSignature, MultiSigner};
	use sp_std::vec::Vec;

	pub fn create_ed25519_pubkey(seed: Vec<u8>) -> MultiSigner {
		ed25519_generate(0.into(), Some(seed)).into()
	}

	pub fn create_ed25519_signature(payload: &[u8], pubkey: MultiSigner) -> MultiSignature {
		let edpubkey = ed25519::Public::try_from(pubkey).unwrap();
		let edsig = ed25519_sign(0.into(), &edpubkey, payload).unwrap();
		edsig.into()
	}

	pub fn signer_to_account_id<T: crate::Config>(
		signer: &MultiSigner,
	) -> Result<T::AccountId, &'static str> {
		T::AccountId::decode(&mut AccountId32::as_ref(&signer.clone().into_account()))
			.map_err(|_| "Could not convert multisigner to account id")
	}
}

benchmarks! {
	where_clause { where <T::Origin as frame_support::traits::OriginTrait>::PalletsOrigin: Clone }
	batch {
		let c in 0 .. 1000;
		let mut calls: Vec<<T as Config>::Call> = Vec::new();
		for i in 0 .. c {
			let call = frame_system::Call::remark { remark: vec![] }.into();
			calls.push(call);
		}
		let caller = whitelisted_caller();
	}: _(RawOrigin::Signed(caller), calls)
	verify {
		assert_last_event::<T>(Event::BatchCompleted.into())
	}

	as_derivative {
		let caller = account("caller", SEED, SEED);
		let call = Box::new(frame_system::Call::remark { remark: vec![] }.into());
		// Whitelist caller account from further DB operations.
		let caller_key = frame_system::Account::<T>::hashed_key_for(&caller);
		frame_benchmarking::benchmarking::add_to_whitelist(caller_key.into());
	}: _(RawOrigin::Signed(caller), SEED as u16, call)

	batch_all {
		let c in 0 .. 1000;
		let mut calls: Vec<<T as Config>::Call> = Vec::new();
		for i in 0 .. c {
			let call = frame_system::Call::remark { remark: vec![] }.into();
			calls.push(call);
		}
		let caller = whitelisted_caller();
	}: _(RawOrigin::Signed(caller), calls)
	verify {
		assert_last_event::<T>(Event::BatchCompleted.into())
	}

	dispatch_as {
		let caller = account("caller", SEED, SEED);
		let call = Box::new(frame_system::Call::remark { remark: vec![] }.into());
		let origin: T::Origin = RawOrigin::Signed(caller).into();
		let pallets_origin: <T::Origin as frame_support::traits::OriginTrait>::PalletsOrigin = origin.caller().clone();
		let pallets_origin = Into::<T::PalletsOrigin>::into(pallets_origin);
	}: _(RawOrigin::Root, Box::new(pallets_origin), call)

	force_batch {
		let c in 0 .. 1000;
		let mut calls: Vec<<T as Config>::Call> = Vec::new();
		for i in 0 .. c {
			let call = frame_system::Call::remark { remark: vec![] }.into();
			calls.push(call);
		}
		let caller = whitelisted_caller();
	}: _(RawOrigin::Signed(caller), calls)
	verify {
		assert_last_event::<T>(Event::BatchCompleted.into())
	}

	submit_call_on_behalf_of {
		let caller: T::AccountId = account("caller", SEED, SEED);
		let call = Box::new(frame_system::Call::remark { remark: vec![] }.into());
		let call_hash = blake2_256(&Encode::encode(&call));
		let signer = crypto::create_ed25519_pubkey(b"//forwarder".to_vec());
		let forwarded_call = ForwardedCall {
			nonce: Default::default(),
			deadline: T::BlockNumber::max_value(),
			call: call,
			signer: signer.clone(),
			whitelisted_forwarder: None,
		};

		let signer_id = crypto::signer_to_account_id::<T>(&signer)?;

		let signature = crypto::create_ed25519_signature(&forwarded_call.encode(), signer);
	}: _(RawOrigin::Signed(caller.clone()), forwarded_call, signature)
	verify {
		assert_last_event::<T>(
			Event::CallForwarded {
				forwarder: caller,
				new_origin: signer_id,
				call_hash,
			}
			.into(),
		);
	}

	impl_benchmark_test_suite!(Pallet, crate::tests::new_test_ext(), crate::tests::Test);
}
