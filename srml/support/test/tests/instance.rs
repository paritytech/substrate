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

#[cfg(feature = "std")]
use serde_derive::Serialize;
use runtime_io::{with_externalities, Blake2Hasher};
use srml_support::rstd::prelude::*;
use srml_support::codec::{Encode, Decode};
use srml_support::runtime_primitives::{generic, Ed25519Signature, testing::H256, BuildStorage};
use srml_support::runtime_primitives::traits::{BlakeTwo256, Block as _, Verify, Digest};
use srml_support::{Parameter, construct_runtime, decl_module, decl_storage, decl_event};

pub trait Currency {
}

// Mock
mod system {
	use super::*;

	pub trait Trait: 'static + Eq + Clone {
		type Origin: Into<Option<RawOrigin<Self::AccountId>>> + From<RawOrigin<Self::AccountId>>;
		type BlockNumber;
		type Digest: Digest<Hash = H256>;
		type AccountId;
		type Event: From<Event>;
		type Log: From<Log<Self>> + Into<DigestItemOf<Self>>;
	}

	pub type DigestItemOf<T> = <<T as Trait>::Digest as Digest>::Item;

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {
			pub fn deposit_event(_event: T::Event) {
			}
		}
	}

	decl_event!(
		pub enum Event {
			ExtrinsicSuccess,
			ExtrinsicFailed,
		}
	);

	/// Origin for the system module.
	#[derive(PartialEq, Eq, Clone)]
	#[cfg_attr(feature = "std", derive(Debug))]
	pub enum RawOrigin<AccountId> {
		Root,
		Signed(AccountId),
		Inherent,
	}

	impl<AccountId> From<Option<AccountId>> for RawOrigin<AccountId> {
		fn from(s: Option<AccountId>) -> RawOrigin<AccountId> {
			match s {
				Some(who) => RawOrigin::Signed(who),
				None => RawOrigin::Inherent,
			}
		}
	}

	pub type Origin<T> = RawOrigin<<T as Trait>::AccountId>;

	pub type Log<T> = RawLog<
		<T as Trait>::AccountId,
	>;

	#[cfg_attr(feature = "std", derive(Serialize, Debug))]
	#[derive(Encode, Decode, PartialEq, Eq, Clone)]
	pub enum RawLog<H> {
		ChangesTrieRoot(H),
	}
}

// TODO TODO: event with no instance, event with only trait and event with trait and instance
// TODO TODO: default instance and no default instance
// TODO TODO: read and write to all kind of storage with different instance
// TODO TODO: user defined instantiable trait
// TODO TODO: inherent, log, origin, config tests

// Test for:
// * Event with Trait but no Instance
// * No default instance
// * Custom InstantiableTrait
mod module1 {
	use super::*;

	pub trait Trait<Instance>: system::Trait {
		type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
	}

	impl<T: Trait<Instance>, Instance: InstantiableThing> Currency for Module<T, Instance> {}

	decl_module! {
		pub struct Module<T: Trait<Instance>, Instance: InstantiableThing> for enum Call where origin: T::Origin {
			fn deposit_event<T>() = default;
		}
	}

	decl_storage! {
		trait Store for Module<T: Trait<Instance>, Instance: InstantiableThing> as Module1 {
			pub Data get(data) config(): linked_map u32 => u64;
			pub Data1 get(data1) config(): map u32 => u64;
			pub Data2 get(data2) config(): u64;
		}
	}

	decl_event! {
		pub enum Event<T> where Digest = <T as system::Trait>::Digest {
			Variant(Digest),
		}
	}
}

// Test for:
// * Event with no Trait
// * Default instance
mod module2 {
	use super::*;

	pub trait Trait<Instance=DefaultInstance>: system::Trait {
		type Event: From<Event> + Into<<Self as system::Trait>::Event>;
	}

	decl_module! {
		pub struct Module<T: Trait<Instance>, Instance: InstantiableThing=DefaultInstance> for enum Call where origin: T::Origin {
			fn deposit_event() = default;
		}
	}

	decl_storage! {
		trait Store for Module<T: Trait<Instance>, Instance: InstantiableThing=DefaultInstance> as Module2 {
			pub Data get(data) build(|_| vec![(15u32, 42u64)]): linked_map u32 => u64;
		}
	}

	decl_event! {
		pub enum Event {
			Variant(u32),
		}
	}
}

// Test for:
// * Event trait and instance
// * use of no_genesis_config_phantom_data
mod module3 {
	use super::*;

	pub trait Trait<Instance=DefaultInstance>: module1::Trait<module1::Instance1> + system::Trait {
		type Amount: Parameter + Default;
		type Event: From<Event<Self, Instance>> + Into<<Self as system::Trait>::Event>;
	}

	decl_module! {
		pub struct Module<T: Trait<Instance>, Instance: Instantiable=DefaultInstance> for enum Call where origin: T::Origin {
			fn deposit_event<T, Instance>() = default;
		}
	}

	decl_storage! {
		trait Store for Module<T: Trait<Instance>, Instance: Instantiable=DefaultInstance> as Module3 {
			pub Data get(data) config(): T::Amount;
		}
		extra_genesis_skip_phantom_data_field;
	}

	decl_event! {
		pub enum Event<T, Instance=DefaultInstance> where Amount = <T as Trait<Instance>>::Amount {
			Variant(Amount),
		}
	}
}

// Test for:
// * Depends on multiple module with instances and default
mod module4 {
	use super::*;

	pub trait Trait: module2::Trait + system::Trait {
		type OtherModule2: module2::Trait<module2::Instance1>;
		type Currency: Currency;
		type Currency2: Currency;
	}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		}
	}
}

// TODO TODO: implement module1
// TODO TODO: implement module1 of another instance
impl module1::Trait<module1::Instance1> for Runtime {
	type Event = Event;
}
impl module2::Trait for Runtime {
	type Event = Event;
}
// TODO TODO: implement module2 of another instance
impl module3::Trait for Runtime {
	type Amount = u32;
	type Event = Event;
}
// // TODO TODO: implement module3 of another instance
// impl module4::Trait for Runtime {
// 	type OtherModule2 = module2::Module<Self, module2::Instance1>;
// 	type Currency = module2::Module<Self, module2::Instance2>;
// 	type Currency2 = module2::Module<Self, module2::Instance3>;
// }

pub type Signature = Ed25519Signature;
pub type AccountId = <Signature as Verify>::Signer;
pub type BlockNumber = u64;
pub type Index = u64;

impl system::Trait for Runtime {
	type Origin = Origin;
	type BlockNumber = BlockNumber;
	type Digest = generic::Digest<Log>;
	type AccountId = AccountId;
	type Event = Event;
	type Log = Log;
}

// TODO TODO: test two generic with event without instance
//            fails: because of implementation.
// TODO TODO: test two generic with config without instance
// TODO TODO: test two generic with log without instance
// TODO TODO: test two generic with origin without instance

construct_runtime!(
	pub enum Runtime with Log(InternalLog: DigestItem<H256, ()>) where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{Module, Call, Event, Log(ChangesTrieRoot)},
		Module1: module1::<Instance1>::{Event<T>},
		// Module1: module1::<Instance2>::{Event<T>},
		Module2: module2::{Module, Call, Storage, Event},
		// Module22: module2::<Instance2>::{Module, Call, Storage, Event},
		// Module23: module2::<Instance3>::{Module, Call, Storage, Event},
		Module3: module3::{Event<T>},
		// Module4: module4::{Module, Call},
	}
);

pub type Header = generic::Header<BlockNumber, BlakeTwo256, Log>;
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = generic::UncheckedMortalCompactExtrinsic<u32, Index, Call, Signature>;

fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
	GenesisConfig{
	}.build_storage().unwrap().0.into()
}

#[test]
fn basic_insert_remove_should_work() {
	with_externalities(&mut new_test_ext(), || {
		// TODO TODO
	});
}
