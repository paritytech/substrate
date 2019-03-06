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
use srml_support::rstd as rstd;
use srml_support::codec::{Encode, Decode};
use srml_support::runtime_primitives::{generic, Ed25519Signature, testing::H256, BuildStorage};
use srml_support::runtime_primitives::traits::{BlakeTwo256, Block as _, Verify, Digest};
use srml_support::{Parameter, construct_runtime, decl_module, decl_storage, decl_event};
use inherents::{
	ProvideInherent, InherentData, InherentIdentifier, RuntimeString, MakeFatalError
};

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

// Test for:
// * No default instance
// * Custom InstantiableTrait
// * Origin, Inherent, Log
mod module1 {
	use super::*;

	pub trait Trait<Instance>: system::Trait {
		type Event: From<Event<Self, Instance>> + Into<<Self as system::Trait>::Event>;
		type Origin: From<Origin<Self, Instance>>;
	}

	decl_module! {
		pub struct Module<T: Trait<Instance>, Instance: InstantiableThing> for enum Call where origin: <T as system::Trait>::Origin {
			fn deposit_event<T, Instance>() = default;
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
		pub enum Event<T, Instance> where Digest = <T as system::Trait>::Digest {
			Variant(Digest),
		}
	}

	#[derive(PartialEq, Eq, Clone)]
	#[cfg_attr(feature = "std", derive(Debug))]
	pub enum Origin<T: Trait<Instance>, Instance> {
		Members(u32),
		_Phantom(rstd::marker::PhantomData<(T, Instance)>),
	}

	pub type Log<T, Instance> = RawLog<
		T,
		Instance,
	>;

	/// A logs in this module.
	#[cfg_attr(feature = "std", derive(serde_derive::Serialize, Debug))]
	#[derive(parity_codec::Encode, parity_codec::Decode, PartialEq, Eq, Clone)]
	pub enum RawLog<T, Instance> {
		_Phantom(rstd::marker::PhantomData<(T, Instance)>),
		AmountChange(u32),
	}

	pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"12345678";

	impl<T: Trait<Instance>, Instance: InstantiableThing> ProvideInherent for Module<T, Instance> {
		type Call = Call<T, Instance>;
		type Error = MakeFatalError<RuntimeString>;
		const INHERENT_IDENTIFIER: InherentIdentifier = INHERENT_IDENTIFIER;

		fn create_inherent(_data: &InherentData) -> Option<Self::Call> {
			unimplemented!();
		}

		fn check_inherent(_call: &Self::Call, _data: &InherentData) -> rstd::result::Result<(), Self::Error> {
			unimplemented!();
		}
	}
}

// Test for:
// * default instance
// * use of no_genesis_config_phantom_data
mod module2 {
	use super::*;

	pub trait Trait<Instance=DefaultInstance>: system::Trait {
		type Amount: Parameter + Default;
		type Event: From<Event<Self, Instance>> + Into<<Self as system::Trait>::Event>;
	}

	impl<T: Trait<Instance>, Instance: Instantiable> Currency for Module<T, Instance> {}

	decl_module! {
		pub struct Module<T: Trait<Instance>, Instance: Instantiable=DefaultInstance> for enum Call where origin: T::Origin {
			fn deposit_event<T, Instance>() = default;
		}
	}

	decl_storage! {
		trait Store for Module<T: Trait<Instance>, Instance: Instantiable=DefaultInstance> as Module2 {
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
// * Depends on multiple instances of a module with instances
mod module3 {
	use super::*;

	pub trait Trait: module2::Trait + module2::Trait<module2::Instance1> + system::Trait {
		type Currency: Currency;
		type Currency2: Currency;
	}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		}
	}
}

impl module1::Trait<module1::Instance1> for Runtime {
	type Event = Event;
	type Origin = Origin;
}
impl module1::Trait<module1::Instance2> for Runtime {
	type Event = Event;
	type Origin = Origin;
}
impl module2::Trait for Runtime {
	type Amount = u16;
	type Event = Event;
}
impl module2::Trait<module2::Instance1> for Runtime {
	type Amount = u32;
	type Event = Event;
}
impl module2::Trait<module2::Instance2> for Runtime {
	type Amount = u32;
	type Event = Event;
}
impl module2::Trait<module2::Instance3> for Runtime {
	type Amount = u64;
	type Event = Event;
}
impl module3::Trait for Runtime {
	type Currency = Module2_2;
	type Currency2 = Module2_3;
}

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

// TODO TODO: try to deposit event inside structure
// TODO TODO: test two generic with log without instance
// TODO TODO: how can we test generation of inherent, log, origin ?

construct_runtime!(
	pub enum Runtime with Log(InternalLog: DigestItem<H256, ()>) where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{Module, Call, Event, Log(ChangesTrieRoot)},
		Module1_1: module1::<Instance1>::{Module, Call, Storage, Event<T, I>, Config<T, I>, Origin<T, I>, Log(), Inherent},
		Module1_2: module1::<Instance2>::{Module, Call, Storage, Event<T, I>, Config<T, I>, Origin<T, I>, Log(), Inherent},
		Module2: module2::{Module, Call, Storage, Event<T>, Config<T>},
		Module2_1: module2::<Instance1>::{Module, Call, Storage, Event<T, I>, Config<T, I>},
		Module2_2: module2::<Instance2>::{Module, Call, Storage, Event<T, I>, Config<T, I>},
		Module2_3: module2::<Instance3>::{Module, Call, Storage, Event<T, I>, Config<T, I>},
		Module3: module3::{Module, Call},
	}
);

pub type Header = generic::Header<BlockNumber, BlakeTwo256, Log>;
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = generic::UncheckedMortalCompactExtrinsic<u32, Index, Call, Signature>;

fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
	GenesisConfig{
		// TODO TODO: better name
		module1ConfigInstance1: None,
		module1ConfigInstance2: None,
		module2: None,
		module2ConfigInstance1: None,
		module2ConfigInstance2: None,
		module2ConfigInstance3: None,
	}.build_storage().unwrap().0.into()
}

#[test]
fn basic_insert_remove_should_work() {
	with_externalities(&mut new_test_ext(), || {
		// TODO TODO: read and write to all kind of storage with different instance
	});
}
