// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

pub trait Trait: frame_system::Config {
	type Balance: frame_support::dispatch::Parameter;
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Config>::Event>;
}

frame_support::decl_storage! {
	trait Store for Module<T: Trait> as Example {
		Dummy get(fn dummy) config(): Option<u32>;
	}
}

frame_support::decl_event!(
	pub enum Event<T>
	where
		B = <T as Trait>::Balance,
	{
		Dummy(B),
	}
);

frame_support::decl_error!(
	pub enum Error for Module<T: Trait> {
		Dummy,
	}
);

frame_support::decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;
		type Error = Error<T>;
		const Foo: u32 = u32::MAX;

		#[weight = 0]
		fn accumulate_dummy(_origin, _increase_by: T::Balance) {
			unimplemented!();
		}

		fn on_initialize(_n: T::BlockNumber) -> frame_support::weights::Weight {
			0
		}
	}
}

impl<T: Trait> sp_runtime::traits::ValidateUnsigned for Module<T> {
	type Call = Call<T>;

	fn validate_unsigned(
		_source: sp_runtime::transaction_validity::TransactionSource,
		_call: &Self::Call,
	) -> sp_runtime::transaction_validity::TransactionValidity {
		unimplemented!();
	}
}

pub const INHERENT_IDENTIFIER: frame_support::inherent::InherentIdentifier = *b"12345678";

impl<T: Trait> frame_support::inherent::ProvideInherent for Module<T> {
	type Call = Call<T>;
	type Error = frame_support::inherent::MakeFatalError<()>;
	const INHERENT_IDENTIFIER: frame_support::inherent::InherentIdentifier = INHERENT_IDENTIFIER;

	fn create_inherent(_data: &frame_support::inherent::InherentData) -> Option<Self::Call> {
		unimplemented!();
	}

	fn check_inherent(
		_: &Self::Call,
		_: &frame_support::inherent::InherentData,
	) -> std::result::Result<(), Self::Error> {
		unimplemented!();
	}

	fn is_inherent(_call: &Self::Call) -> bool {
		unimplemented!();
	}
}

#[cfg(test)]
mod tests {
	use crate as pallet_test;

	use frame_support::parameter_types;

	type SignedExtra = (
		frame_system::CheckEra<Runtime>,
		frame_system::CheckNonce<Runtime>,
		frame_system::CheckWeight<Runtime>,
	);
	type TestBlock = sp_runtime::generic::Block<TestHeader, TestUncheckedExtrinsic>;
	type TestHeader = sp_runtime::generic::Header<u64, sp_runtime::traits::BlakeTwo256>;
	type TestUncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<
		<Runtime as frame_system::Config>::AccountId,
		<Runtime as frame_system::Config>::Call,
		(),
		SignedExtra,
	>;

	frame_support::construct_runtime!(
		pub enum Runtime where
			Block = TestBlock,
			NodeBlock = TestBlock,
			UncheckedExtrinsic = TestUncheckedExtrinsic
		{
			System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
			PalletTest: pallet_test::{Pallet, Call, Storage, Event<T>, Config, ValidateUnsigned, Inherent},
		}
	);

	parameter_types! {
		pub const BlockHashCount: u64 = 250;
	}

	impl frame_system::Config for Runtime {
		type BaseCallFilter = frame_support::traits::AllowAll;
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = sp_core::H256;
		type Call = Call;
		type Hashing = sp_runtime::traits::BlakeTwo256;
		type AccountId = u64;
		type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
		type Header = TestHeader;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type DbWeight = ();
		type BlockWeights = ();
		type BlockLength = ();
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
		type OnSetCode = ();
	}

	impl pallet_test::Trait for Runtime {
		type Balance = u32;
		type Event = ();
	}
}
