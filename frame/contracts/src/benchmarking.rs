// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Benchmarks for the contracts pallet

#![cfg(feature = "runtime-benchmarks")]

use crate::*;
use crate::Module as Contracts;

use frame_benchmarking::{benchmarks, account};
use frame_system::{Module as System, RawOrigin};
use parity_wasm::elements::FuncBody;
use sp_runtime::traits::Hash;

macro_rules! load_module {
	($name:expr) => {{
		let code = include_bytes!(concat!("../fixtures/benchmarks/", $name, ".wat"));
		compile_module::<T>(code)
	}};
}

fn compile_module<T: Trait>(code: &[u8]) -> (Vec<u8>, <T::Hashing as Hash>::Output) {
	let code = sp_std::str::from_utf8(code).expect("Invalid utf8 in wat file.");
	let binary = wat::parse_str(code).expect("Failed to compile wat file.");
	let hash = T::Hashing::hash(&binary);
	(binary, hash)
}

fn funding<T: Trait>() -> BalanceOf<T> {
	T::Currency::minimum_balance() * 10_000.into()
}

fn create_funded_user<T: Trait>(string: &'static str, n: u32) -> T::AccountId {
	let user = account(string, n, 0);
	T::Currency::make_free_balance_be(&user, funding::<T>());
	user
}

fn contract_with_call_body<T: Trait>(body: FuncBody) -> (Vec<u8>, <T::Hashing as Hash>::Output) {
	use parity_wasm::elements::{
		Instructions, Instruction::End,
	};
	let contract = parity_wasm::builder::ModuleBuilder::new()
		// deploy function (idx 0)
		.function()
			.signature().with_params(vec![]).with_return_type(None).build()
			.body().with_instructions(Instructions::new(vec![End])).build()
			.build()
		// call function (idx 1)
		.function()
			.signature().with_params(vec![]).with_return_type(None).build()
			.with_body(body)
			.build()
		.export().field("deploy").internal().func(0).build()
		.export().field("call").internal().func(1).build()
		.build();
	let bytes = contract.to_bytes().unwrap();
	let hash = T::Hashing::hash(&bytes);
	(bytes, hash)
}

fn expanded_contract<T: Trait>(target_bytes: u32) -> (Vec<u8>, <T::Hashing as Hash>::Output) {
	use parity_wasm::elements::{
		Instruction::{self, If, I32Const, Return, End},
		BlockType, Instructions,
	};
	// Base size of a contract is 47 bytes and each expansion adds 6 bytes.
	// We do one expansion less to account for the code section and function body
	// size fields inside the binary wasm module representation which are leb128 encoded
	// and therefore grow in size when the contract grows. We are not allowed to overshoot
	// because of the maximum code size that is enforced by `put_code`.
	let expansions = (target_bytes.saturating_sub(47) / 6).saturating_sub(1) as usize;
	const EXPANSION: [Instruction; 4] = [
		I32Const(0),
		If(BlockType::NoResult),
		Return,
		End,
	];
	let instructions = Instructions::new(
		EXPANSION
			.iter()
			.cycle()
			.take(EXPANSION.len() * expansions)
			.cloned()
			.chain(sp_std::iter::once(End))
			.collect()
	);
	contract_with_call_body::<T>(FuncBody::new(Vec::new(), instructions))
}

fn advance_block<T: Trait>(num: <T as frame_system::Trait>::BlockNumber) {
	let now = System::<T>::block_number();
	System::<T>::set_block_number(now + num);
}

benchmarks! {
	_ {
	}

	// This extrinsic is pretty much constant as it is only a simple setter.
	update_schedule {
		let schedule = Schedule {
			version: 1,
			.. Default::default()
		};
	}: _(RawOrigin::Root, schedule)

	// This constructs a contract that is maximal expensive to instrument.
	// It creates a maximum number of metering blocks per byte.
	put_code {
		let n in 0 .. Contracts::<T>::current_schedule().max_code_size;
		let caller = create_funded_user::<T>("caller", 0);
		let (binary, hash) = expanded_contract::<T>(n);
	}: _(RawOrigin::Signed(caller), binary)

	// Instantiate uses a dummy contract constructor to measure the overhead of the instantiate.
	// The size of the data has no influence on the costs of this extrinsic as long as the contract
	// won't call `seal_input` in its constructor to copy the data to contract memory.
	// The dummy contract used here does not do this. The costs for the data copy is billed as
	// part of `seal_input`.
	instantiate {
		let data = vec![0u8; 128];
		let endowment = Config::<T>::subsistence_threshold_uncached();
		let caller = create_funded_user::<T>("caller", 0);
		let (binary, hash) = load_module!("dummy");
		Contracts::<T>::put_code(RawOrigin::Signed(caller.clone()).into(), binary.to_vec())
			.unwrap();

	}: _(
			RawOrigin::Signed(caller.clone()),
			endowment,
			Weight::max_value(),
			hash,
			data
		)
	verify {
		assert_eq!(
			funding::<T>() - endowment,
			T::Currency::free_balance(&caller),
		)
	}

	// We just call a dummy contract to measure to overhead of the call extrinsic.
	// As for instantiate the size of the data does not influence the costs.
	call {
		let data = vec![0u8; 128];
		let endowment = Config::<T>::subsistence_threshold_uncached();
		let value = T::Currency::minimum_balance() * 100.into();
		let caller = create_funded_user::<T>("caller", 0);
		let (binary, hash) = load_module!("dummy");
		let addr = T::DetermineContractAddress::contract_address_for(&hash, &[], &caller);
		Contracts::<T>::put_code(RawOrigin::Signed(caller.clone()).into(), binary.to_vec())
			.unwrap();
		Contracts::<T>::instantiate(
			RawOrigin::Signed(caller.clone()).into(),
			endowment,
			Weight::max_value(),
			hash,
			vec![],
		).unwrap();
	}: _(
			RawOrigin::Signed(caller.clone()),
			T::Lookup::unlookup(addr),
			value,
			Weight::max_value(),
			data
		)
	verify {
		assert_eq!(
			funding::<T>() - endowment - value,
			T::Currency::free_balance(&caller),
		)
	}

	// We benchmark the costs for sucessfully evicting an empty contract.
	// The actual costs are depending on how many storage items the evicted contract
	// does have. However, those costs are not to be payed by the sender but
	// will be distributed over multiple blocks using a scheduler. Otherwise there is
	// no incentive to remove large contracts when the removal is more expensive than
	// the reward for removing them.
	claim_surcharge {
		let endowment = Config::<T>::subsistence_threshold_uncached();
		let value = T::Currency::minimum_balance() * 100.into();
		let caller = create_funded_user::<T>("caller", 0);
		let (binary, hash) = load_module!("dummy");
		let addr = T::DetermineContractAddress::contract_address_for(&hash, &[], &caller);
		Contracts::<T>::put_code(RawOrigin::Signed(caller.clone()).into(), binary.to_vec())
			.unwrap();
		Contracts::<T>::instantiate(
			RawOrigin::Signed(caller.clone()).into(),
			endowment,
			Weight::max_value(),
			hash,
			vec![],
		).unwrap();

		// instantiate should leave us with an alive contract
		ContractInfoOf::<T>::get(addr.clone()).unwrap().get_alive().unwrap();

		// generate some rent
		advance_block::<T>(<T as Trait>::SignedClaimHandicap::get() + 1.into());

	}: _(RawOrigin::Signed(caller.clone()), addr.clone(), None)
	verify {
		// the claim surcharge should have evicted the contract
		ContractInfoOf::<T>::get(addr.clone()).unwrap().get_tombstone().unwrap();

		// the caller should get the reward for being a good snitch
		assert_eq!(
			funding::<T>() - endowment + <T as Trait>::SurchargeReward::get(),
			T::Currency::free_balance(&caller),
		);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{ExtBuilder, Test};
	use frame_support::assert_ok;

	#[test]
	fn update_schedule() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_update_schedule::<Test>());
		});
	}

	#[test]
	fn put_code() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_put_code::<Test>());
		});
	}

	#[test]
	fn instantiate() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_instantiate::<Test>());
		});
	}

	#[test]
	fn call() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_call::<Test>());
		});
	}

	#[test]
	fn claim_surcharge() {
		ExtBuilder::default().build().execute_with(|| {
			assert_ok!(test_benchmark_claim_surcharge::<Test>());
		});
	}
}
