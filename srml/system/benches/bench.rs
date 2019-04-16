// Copyright 2019 Parity Technologies (UK) Ltd.
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

use criterion::{Criterion, criterion_group, criterion_main, black_box};
use srml_system as system;
use srml_support::{decl_module, decl_event, impl_outer_origin, impl_outer_event};
use runtime_io::{with_externalities, Blake2Hasher};
use substrate_primitives::H256;
use primitives::{
	BuildStorage, traits::{BlakeTwo256, IdentityLookup},
	testing::{Digest, DigestItem, Header},
};

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
		module,
	}
}

#[derive(Clone, Eq, PartialEq)]
pub struct Runtime;
impl system::Trait for Runtime {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type Digest = Digest;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type Log = DigestItem;
}

impl module::Trait for Runtime {
	type Event = Event;
}

fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
	system::GenesisConfig::<Runtime>::default().build_storage().unwrap().0.into()
}

fn deposit_events(n: usize) {
	let mut t = new_test_ext();
	with_externalities(&mut t, || {
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
