// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

#![cfg(test)]

//use crate::GetMigrations;
use crate::Config;
use core::cell::RefCell;
use sp_core::Get;
use codec::{Decode, Encode};
use frame_support::{
	migrations::*,
	traits::{ConstU16, ConstU64, OnFinalize, OnInitialize},
	weights::{Weight, WeightMeter},
};
use sp_core::{ConstU32, H256};
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
	BoundedVec,
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

// Configure a mock runtime to test the pallet.
frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system,
		Migrations: crate,
	}
);

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ConstU16<42>;
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
pub enum MockedMigrationKind {
	SucceedAfter,
	FailAfter,
}
use MockedMigrationKind::*; // C style

pub struct MockedMigrate(MockedMigrationKind, u32);

impl SteppedMigration for MockedMigrate {
	type Cursor = BoundedVec<u8, ConstU32<1024>>;
	type Identifier = BoundedVec<u8, ConstU32<32>>;

	fn id(&self) -> Self::Identifier {
		mocked_id(self.0, self.1)
	}

	fn step(
		&self,
		cursor: &Option<Self::Cursor>,
		_meter: &mut WeightMeter,
	) -> Result<Option<Self::Cursor>, SteppedMigrationError> {
		let mut count: u32 =
			cursor.as_ref().and_then(|c| Decode::decode(&mut &c[..]).ok()).unwrap_or(0);
		log::debug!("MockedMigrate: Step {}", count);
		if count != self.1 {
			count += 1;
			return Ok(Some(count.encode().try_into().unwrap()))
		}

		match self.0 {
			SucceedAfter => {
				log::debug!("MockedMigrate: Succeeded after {} steps", count);
				Ok(None)
			},
			FailAfter => {
				log::debug!("MockedMigrate: Failed after {} steps", count);
				Err(SteppedMigrationError::Failed)
			},
		}
	}
}

type MockedCursor = BoundedVec<u8, ConstU32<1024>>;
type MockedIdentifier = BoundedVec<u8, ConstU32<32>>;

frame_support::parameter_types! {
	pub const ServiceWeight: Weight = Weight::MAX;
}

thread_local! {
	pub static MIGRATIONS: RefCell<Vec<(MockedMigrationKind, u32)>> = RefCell::new(vec![]);
}

pub struct MigrationsStorage;
impl Get<Vec<Box<dyn SteppedMigration<Cursor=MockedCursor, Identifier=MockedIdentifier>>>> for MigrationsStorage {
	fn get() -> Vec<Box<dyn SteppedMigration<Cursor=MockedCursor, Identifier=MockedIdentifier>>> {
		MIGRATIONS.with(|m|
			m.borrow().clone().into_iter().map(|(k, v)| Box::new(MockedMigrate(k, v)) as Box<dyn SteppedMigration<Cursor=MockedCursor, Identifier=MockedIdentifier>>).collect()
		)
	}
}

fn mocked_id(kind: MockedMigrationKind, steps: u32) -> MockedIdentifier {
	format!("MockedMigrate({:?}, {})", kind, steps)
		.as_bytes()
		.to_vec()
		.try_into()
		.unwrap()
}

impl crate::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type Migrations = MigrationsStorage;
	type Cursor = MockedCursor;
	type Identifier = MockedIdentifier;
	type ServiceWeight = ServiceWeight;
	type WeightInfo = ();
}

// Build genesis storage according to the mock runtime.
pub fn new_test_ext() -> sp_io::TestExternalities {
	frame_system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
}

pub struct LoggingSuspender<Inner>(core::marker::PhantomData<Inner>);
impl<Inner: ExtrinsicSuspenderQuery> ExtrinsicSuspenderQuery for LoggingSuspender<Inner> {
	fn is_suspended() -> bool {
		let res = Inner::is_suspended();
		log::debug!("IsSuspended: {res}");
		res
	}
}

pub fn assert_last_event<T: Config>(generic_event: <T as Config>::RuntimeEvent) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

pub fn run_to_block(n: u64) {
	while System::block_number() < n {
		if System::block_number() > 1 {
			Migrations::on_finalize(System::block_number());
			System::on_finalize(System::block_number());
		}
		log::debug!("Block {}", System::block_number());
		System::set_block_number(System::block_number() + 1);
		System::on_initialize(System::block_number());
		Migrations::on_initialize(System::block_number());
	}
}
