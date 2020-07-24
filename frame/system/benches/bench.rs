// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

use criterion::{Criterion, criterion_group, criterion_main, black_box};
use frame_system as system;
use frame_support::{decl_module, decl_event, impl_outer_origin, impl_outer_event, weights::Weight};
use sp_core::H256;
use sp_runtime::{Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header};

mod module {
	use super::*;

	pub trait Trait: system::Trait {
		type Event: From<Event> + Into<<Self as system::Trait>::Event>;
	}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {
			pub fn deposit_event() = default;
		}
	}

	decl_event!(
		pub enum Event {
			Complex(Vec<u8>, u32, u16, u128),
		}
	);
}

impl_outer_origin!{
	pub enum Origin for Runtime {}
}

impl_outer_event! {
	pub enum Event for Runtime {
		system<T>,
		module,
	}
}

frame_support::parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 4 * 1024 * 1024;
	pub const MaximumBlockLength: u32 = 4 * 1024 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::from_percent(75);
}
#[derive(Clone, Eq, PartialEq)]
pub struct Runtime;
impl system::Trait for Runtime {
	type BaseCallFilter = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = ();
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumExtrinsicWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
}

impl module::Trait for Runtime {
	type Event = Event;
}

fn new_test_ext() -> sp_io::TestExternalities {
	system::GenesisConfig::default().build_storage::<Runtime>().unwrap().into()
}

fn deposit_events(n: usize) {
	let mut t = new_test_ext();
	t.execute_with(|| {
		for _ in 0..n {
			module::Module::<Runtime>::deposit_event(
				module::Event::Complex(vec![1, 2, 3], 2, 3, 899)
			);
		}
	});
}

fn sr_system_benchmark(c: &mut Criterion) {
	c.bench_function("deposit 100 events", |b| {
		b.iter(|| deposit_events(black_box(100)))
	});
}

criterion_group!(benches, sr_system_benchmark);
criterion_main!(benches);
