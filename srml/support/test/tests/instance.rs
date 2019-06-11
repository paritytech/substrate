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

#![recursion_limit="128"]

#[cfg(feature = "std")]
use serde::Serialize;
use runtime_io::{with_externalities, Blake2Hasher};
use srml_support::rstd::prelude::*;
use srml_support::rstd as rstd;
use srml_support::codec::{Encode, Decode};
use srml_support::runtime_primitives::{generic, BuildStorage};
use srml_support::runtime_primitives::traits::{BlakeTwo256, Block as _, Verify, Digest};
use srml_support::Parameter;
use inherents::{
	ProvideInherent, InherentData, InherentIdentifier, RuntimeString, MakeFatalError
};
use srml_support::{StorageValue, StorageMap, StorageDoubleMap};
use primitives::{H256, sr25519};

pub trait Currency {
}

// Mock
mod system {
	use super::*;

	pub trait Trait: 'static + Eq + Clone {
		type Origin: Into<Result<RawOrigin<Self::AccountId>, Self::Origin>>
			+ From<RawOrigin<Self::AccountId>>;
		type BlockNumber;
		type Digest: Digest<Hash = H256>;
		type Hash;
		type AccountId;
		type Event: From<Event>;
		type Log: From<Log<Self>> + Into<DigestItemOf<Self>>;
	}

	pub type DigestItemOf<T> = <<T as Trait>::Digest as Digest>::Item;

	srml_support::decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {
			pub fn deposit_event(_event: T::Event) {
			}
		}
	}
	impl<T: Trait> Module<T> {
		pub fn deposit_log(_item: <T::Digest as Digest>::Item) {
			unimplemented!();
		}
	}

	srml_support::decl_event!(
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
		None,
	}

	impl<AccountId> From<Option<AccountId>> for RawOrigin<AccountId> {
		fn from(s: Option<AccountId>) -> RawOrigin<AccountId> {
			match s {
				Some(who) => RawOrigin::Signed(who),
				None => RawOrigin::None,
			}
		}
	}

	pub type Origin<T> = RawOrigin<<T as Trait>::AccountId>;

	pub type Log<T> = RawLog<
		<T as Trait>::Hash,
	>;

	#[cfg_attr(feature = "std", derive(Serialize, Debug))]
	#[derive(Encode, Decode, PartialEq, Eq, Clone)]
	pub enum RawLog<H> {
		ChangesTrieRoot(H),
	}

	pub fn ensure_root<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<(), &'static str>
		where OuterOrigin: Into<Result<RawOrigin<AccountId>, OuterOrigin>>
	{
		o.into().map(|_| ()).map_err(|_| "bad origin: expected to be a root origin")
	}
}

// Test for:
// * No default instance
// * Custom InstantiableTrait
// * Origin, Inherent, Log, Event
mod module1 {
	use super::*;

	pub trait Trait<I>: system::Trait {
		type Event: From<Event<Self, I>> + Into<<Self as system::Trait>::Event>;
		type Origin: From<Origin<Self, I>>;
		type Log: From<Log<Self, I>> + Into<system::DigestItemOf<Self>>;
	}

	srml_support::decl_module! {
		pub struct Module<T: Trait<I>, I: InstantiableThing> for enum Call where origin: <T as system::Trait>::Origin {
			fn deposit_event<T, I>() = default;

			fn one() {
				Self::deposit_event(RawEvent::AnotherVariant(3));
				Self::deposit_log(RawLog::AmountChange(3));
			}
		}
	}

	impl<T: Trait<I>, I: InstantiableThing> Module<T, I> {
		/// Deposit one of this module's logs.
		fn deposit_log(log: Log<T, I>) {
			<system::Module<T>>::deposit_log(<T as Trait<I>>::Log::from(log).into());
		}
	}

	srml_support::decl_storage! {
		trait Store for Module<T: Trait<I>, I: InstantiableThing> as Module1 {
			pub Value config(value): u64;
			pub Map: map u32 => u64;
			pub LinkedMap: linked_map u32 => u64;
		}
	}

	srml_support::decl_event! {
		pub enum Event<T, I> where Phantom = rstd::marker::PhantomData<T> {
			_Phantom(Phantom),
			AnotherVariant(u32),
		}
	}

	#[derive(PartialEq, Eq, Clone)]
	#[cfg_attr(feature = "std", derive(Debug))]
	pub enum Origin<T: Trait<I>, I> {
		Members(u32),
		_Phantom(rstd::marker::PhantomData<(T, I)>),
	}

	pub type Log<T, I> = RawLog<
		T,
		I,
		<T as system::Trait>::Hash,
	>;

	/// A logs in this module.
	#[cfg_attr(feature = "std", derive(serde::Serialize, Debug))]
	#[derive(parity_codec::Encode, parity_codec::Decode, PartialEq, Eq, Clone)]
	pub enum RawLog<T, I, Hash> {
		_Phantom(rstd::marker::PhantomData<(T, I)>),
		AmountChange(u32),
		ChangesTrieRoot(Hash),
		AuthoritiesChange(Vec<()>),
	}

	pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"12345678";

	impl<T: Trait<I>, I: InstantiableThing> ProvideInherent for Module<T, I> {
		type Call = Call<T, I>;
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

	pub trait Trait<I=DefaultInstance>: system::Trait {
		type Amount: Parameter + Default;
		type Event: From<Event<Self, I>> + Into<<Self as system::Trait>::Event>;
		type Origin: From<Origin<Self, I>>;
		type Log: From<Log<Self, I>> + Into<system::DigestItemOf<Self>>;
	}

	impl<T: Trait<I>, I: Instance> Currency for Module<T, I> {}

	srml_support::decl_module! {
		pub struct Module<T: Trait<I>, I: Instance=DefaultInstance> for enum Call where origin: <T as system::Trait>::Origin {
			fn deposit_event<T, I>() = default;
		}
	}

	srml_support::decl_storage! {
		trait Store for Module<T: Trait<I>, I: Instance=DefaultInstance> as Module2 {
			pub Value config(value): T::Amount;
			pub Map config(map): map u64 => u64;
			pub LinkedMap config(linked_map): linked_map u64 => u64;
			pub DoubleMap config(double_map): double_map u64, blake2_256(u64) => u64;
		}
		extra_genesis_skip_phantom_data_field;
	}

	srml_support::decl_event! {
		pub enum Event<T, I=DefaultInstance> where Amount = <T as Trait<I>>::Amount {
			Variant(Amount),
		}
	}

	#[derive(PartialEq, Eq, Clone)]
	#[cfg_attr(feature = "std", derive(Debug))]
	pub enum Origin<T: Trait<I>, I=DefaultInstance> {
		Members(u32),
		_Phantom(rstd::marker::PhantomData<(T, I)>),
	}

	pub type Log<T, I=DefaultInstance> = RawLog<
		T,
		I,
	>;

	/// A logs in this module.
	#[cfg_attr(feature = "std", derive(serde::Serialize, Debug))]
	#[derive(parity_codec::Encode, parity_codec::Decode, PartialEq, Eq, Clone)]
	pub enum RawLog<T, I=DefaultInstance> {
		_Phantom(rstd::marker::PhantomData<(T, I)>),
		AmountChange(u32),
	}

	pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"12345678";

	impl<T: Trait<I>, I: Instance> ProvideInherent for Module<T, I> {
		type Call = Call<T, I>;
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
// * Depends on multiple instances of a module with instances
mod module3 {
	use super::*;

	pub trait Trait: module2::Trait + module2::Trait<module2::Instance1> + system::Trait {
		type Currency: Currency;
		type Currency2: Currency;
	}

	srml_support::decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: <T as system::Trait>::Origin {
		}
	}
}

impl module1::Trait<module1::Instance1> for Runtime {
	type Event = Event;
	type Origin = Origin;
	type Log = Log;
}
impl module1::Trait<module1::Instance2> for Runtime {
	type Event = Event;
	type Origin = Origin;
	type Log = Log;
}
impl module2::Trait for Runtime {
	type Amount = u16;
	type Event = Event;
	type Origin = Origin;
	type Log = Log;
}
impl module2::Trait<module2::Instance1> for Runtime {
	type Amount = u32;
	type Event = Event;
	type Origin = Origin;
	type Log = Log;
}
impl module2::Trait<module2::Instance2> for Runtime {
	type Amount = u32;
	type Event = Event;
	type Origin = Origin;
	type Log = Log;
}
impl module2::Trait<module2::Instance3> for Runtime {
	type Amount = u64;
	type Event = Event;
	type Origin = Origin;
	type Log = Log;
}
impl module3::Trait for Runtime {
	type Currency = Module2_2;
	type Currency2 = Module2_3;
}

pub type Signature = sr25519::Signature;
pub type AccountId = <Signature as Verify>::Signer;
pub type BlockNumber = u64;
pub type Index = u64;

impl system::Trait for Runtime {
	type Hash = H256;
	type Origin = Origin;
	type BlockNumber = BlockNumber;
	type Digest = generic::Digest<Log>;
	type AccountId = AccountId;
	type Event = Event;
	type Log = Log;
}

srml_support::construct_runtime!(
	pub enum Runtime with Log(InternalLog: DigestItem<H256, (), ()>) where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{Module, Call, Event, Log(ChangesTrieRoot)},
		Module1_1: module1::<Instance1>::{Module, Call, Storage, Event<T, I>, Config<T, I>, Origin<T, I>, Log(ChangesTrieRoot, AuthoritiesChange), Inherent},
		Module1_2: module1::<Instance2>::{Module, Call, Storage, Event<T, I>, Config<T, I>, Origin<T, I>, Log(ChangesTrieRoot, AuthoritiesChange), Inherent},
		Module2: module2::{Module, Call, Storage, Event<T>, Config<T>, Origin<T>, Log(), Inherent},
		Module2_1: module2::<Instance1>::{Module, Call, Storage, Event<T, I>, Config<T, I>, Origin<T, I>, Log(), Inherent},
		Module2_2: module2::<Instance2>::{Module, Call, Storage, Event<T, I>, Config<T, I>, Origin<T, I>, Log(), Inherent},
		Module2_3: module2::<Instance3>::{Module, Call, Storage, Event<T, I>, Config<T, I>, Origin<T, I>, Log(), Inherent},
		Module3: module3::{Module, Call},
	}
);

pub type Header = generic::Header<BlockNumber, BlakeTwo256, Log>;
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = generic::UncheckedMortalCompactExtrinsic<u32, Index, Call, Signature>;

fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
	GenesisConfig{
		module1_Instance1: Some(module1::GenesisConfig {
			value: 3,
			.. Default::default()
		}),
		module1_Instance2: Some(module1::GenesisConfig {
			value: 4,
			_genesis_phantom_data: Default::default(),
		}),
		module2: Some(module2::GenesisConfig {
			value: 4,
			map: vec![(0, 0)],
			linked_map: vec![(0, 0)],
			double_map: vec![(0, 0, 0)],
		}),
		module2_Instance1: Some(module2::GenesisConfig {
			value: 4,
			map: vec![(0, 0)],
			linked_map: vec![(0, 0)],
			double_map: vec![(0, 0, 0)],
		}),
		module2_Instance2: None,
		module2_Instance3: None,
	}.build_storage().unwrap().0.into()
}

#[test]
fn storage_instance_independance() {
	with_externalities(&mut new_test_ext(), || {
		let mut map = rstd::collections::btree_map::BTreeMap::new();
		for key in [
			module2::Value::<Runtime>::key().to_vec(),
			module2::Value::<Runtime, module2::Instance1>::key().to_vec(),
			module2::Value::<Runtime, module2::Instance2>::key().to_vec(),
			module2::Value::<Runtime, module2::Instance3>::key().to_vec(),
			module2::Map::<Runtime>::prefix().to_vec(),
			module2::Map::<Runtime, module2::Instance1>::prefix().to_vec(),
			module2::Map::<Runtime, module2::Instance2>::prefix().to_vec(),
			module2::Map::<Runtime, module2::Instance3>::prefix().to_vec(),
			module2::LinkedMap::<Runtime>::prefix().to_vec(),
			module2::LinkedMap::<Runtime, module2::Instance1>::prefix().to_vec(),
			module2::LinkedMap::<Runtime, module2::Instance2>::prefix().to_vec(),
			module2::LinkedMap::<Runtime, module2::Instance3>::prefix().to_vec(),
			module2::DoubleMap::<Runtime>::prefix().to_vec(),
			module2::DoubleMap::<Runtime, module2::Instance1>::prefix().to_vec(),
			module2::DoubleMap::<Runtime, module2::Instance2>::prefix().to_vec(),
			module2::DoubleMap::<Runtime, module2::Instance3>::prefix().to_vec(),
			module2::Map::<Runtime>::key_for(0),
			module2::Map::<Runtime, module2::Instance1>::key_for(0).to_vec(),
			module2::Map::<Runtime, module2::Instance2>::key_for(0).to_vec(),
			module2::Map::<Runtime, module2::Instance3>::key_for(0).to_vec(),
			module2::LinkedMap::<Runtime>::key_for(0),
			module2::LinkedMap::<Runtime, module2::Instance1>::key_for(0).to_vec(),
			module2::LinkedMap::<Runtime, module2::Instance2>::key_for(0).to_vec(),
			module2::LinkedMap::<Runtime, module2::Instance3>::key_for(0).to_vec(),
			module2::Map::<Runtime>::key_for(1),
			module2::Map::<Runtime, module2::Instance1>::key_for(1).to_vec(),
			module2::Map::<Runtime, module2::Instance2>::key_for(1).to_vec(),
			module2::Map::<Runtime, module2::Instance3>::key_for(1).to_vec(),
			module2::LinkedMap::<Runtime>::key_for(1),
			module2::LinkedMap::<Runtime, module2::Instance1>::key_for(1).to_vec(),
			module2::LinkedMap::<Runtime, module2::Instance2>::key_for(1).to_vec(),
			module2::LinkedMap::<Runtime, module2::Instance3>::key_for(1).to_vec(),
			module2::DoubleMap::<Runtime>::prefix_for(1),
			module2::DoubleMap::<Runtime, module2::Instance1>::prefix_for(1).to_vec(),
			module2::DoubleMap::<Runtime, module2::Instance2>::prefix_for(1).to_vec(),
			module2::DoubleMap::<Runtime, module2::Instance3>::prefix_for(1).to_vec(),
			module2::DoubleMap::<Runtime>::key_for(1, 1),
			module2::DoubleMap::<Runtime, module2::Instance1>::key_for(1, 1).to_vec(),
			module2::DoubleMap::<Runtime, module2::Instance2>::key_for(1, 1).to_vec(),
			module2::DoubleMap::<Runtime, module2::Instance3>::key_for(1, 1).to_vec(),
		].iter() {
			assert!(map.insert(key, ()).is_none())
		}
	});
}

#[test]
fn storage_with_instance_basic_operation() {
	with_externalities(&mut new_test_ext(), || {
		type Value = module2::Value<Runtime, module2::Instance1>;
		type Map = module2::Map<Runtime, module2::Instance1>;
		type LinkedMap = module2::LinkedMap<Runtime, module2::Instance1>;
		type DoubleMap = module2::DoubleMap<Runtime, module2::Instance1>;

		assert_eq!(Value::exists(), true);
		assert_eq!(Value::get(), 4);
		Value::put(1);
		assert_eq!(Value::get(), 1);
		assert_eq!(Value::take(), 1);
		assert_eq!(Value::get(), 0);
		Value::mutate(|a| *a=2);
		assert_eq!(Value::get(), 2);
		Value::kill();
		assert_eq!(Value::exists(), false);
		assert_eq!(Value::get(), 0);

		let key = 1;
		assert_eq!(Map::exists(0), true);
		assert_eq!(Map::exists(key), false);
		Map::insert(key, 1);
		assert_eq!(Map::get(key), 1);
		assert_eq!(Map::take(key), 1);
		assert_eq!(Map::get(key), 0);
		Map::mutate(key, |a| *a=2);
		assert_eq!(Map::get(key), 2);
		Map::remove(key);
		assert_eq!(Map::exists(key), false);
		assert_eq!(Map::get(key), 0);

		assert_eq!(LinkedMap::exists(0), true);
		assert_eq!(LinkedMap::exists(key), false);
		LinkedMap::insert(key, 1);
		assert_eq!(LinkedMap::get(key), 1);
		assert_eq!(LinkedMap::take(key), 1);
		assert_eq!(LinkedMap::get(key), 0);
		LinkedMap::mutate(key, |a| *a=2);
		assert_eq!(LinkedMap::get(key), 2);
		LinkedMap::remove(key);
		assert_eq!(LinkedMap::exists(key), false);
		assert_eq!(LinkedMap::get(key), 0);

		let key1 = 1;
		let key2 = 1;
		assert_eq!(DoubleMap::exists(0, 0), true);
		assert_eq!(DoubleMap::exists(key1, key2), false);
		DoubleMap::insert(key1, key2, 1);
		assert_eq!(DoubleMap::get(key1, key2), 1);
		assert_eq!(DoubleMap::take(key1, key2), 1);
		assert_eq!(DoubleMap::get(key1, key2), 0);
		DoubleMap::mutate(key1, key2, |a| *a=2);
		assert_eq!(DoubleMap::get(key1, key2), 2);
		DoubleMap::remove(key1, key2);
		assert_eq!(DoubleMap::get(key1, key2), 0);
	});
}
