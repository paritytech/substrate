// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! General tests for construct_runtime macro, test for:
//! * error declareed with decl_error works
//! * integrity test is generated

#![recursion_limit = "128"]

use frame_support::traits::PalletInfo as _;
use sp_core::{sr25519, H256};
use sp_runtime::{
	generic,
	traits::{BlakeTwo256, Verify},
	DispatchError,
};
use sp_std::cell::RefCell;

mod system;

pub trait Currency {}

thread_local! {
	pub static INTEGRITY_TEST_EXEC: RefCell<u32> = RefCell::new(0);
}

mod module1 {
	use super::*;

	pub trait Config<I>: system::Config {}

	frame_support::decl_module! {
		pub struct Module<T: Config<I>, I: Instance = DefaultInstance> for enum Call
			where origin: <T as system::Config>::Origin, system=system
		{
			#[weight = 0]
			pub fn fail(_origin) -> frame_support::dispatch::DispatchResult {
				Err(Error::<T, I>::Something.into())
			}
		}
	}

	#[derive(Clone, PartialEq, Eq, Debug, codec::Encode, codec::Decode)]
	pub struct Origin<T, I: Instance = DefaultInstance>(pub core::marker::PhantomData<(T, I)>);

	frame_support::decl_event! {
		pub enum Event<T, I: Instance = DefaultInstance> where
			<T as system::Config>::AccountId
		{
			A(AccountId),
		}
	}

	frame_support::decl_error! {
		pub enum Error for Module<T: Config<I>, I: Instance> {
			Something
		}
	}

	frame_support::decl_storage! {
		trait Store for Module<T: Config<I>, I: Instance=DefaultInstance> as Module {}
	}
}

mod module2 {
	use super::*;

	pub trait Config: system::Config {}

	frame_support::decl_module! {
		pub struct Module<T: Config> for enum Call
			where origin: <T as system::Config>::Origin, system=system
		{
			#[weight = 0]
			pub fn fail(_origin) -> frame_support::dispatch::DispatchResult {
				Err(Error::<T>::Something.into())
			}

			fn integrity_test() {
				INTEGRITY_TEST_EXEC.with(|i| *i.borrow_mut() += 1);
			}
		}
	}

	#[derive(Clone, PartialEq, Eq, Debug, codec::Encode, codec::Decode)]
	pub struct Origin;

	frame_support::decl_event! {
		pub enum Event {
			A,
		}
	}

	frame_support::decl_error! {
		pub enum Error for Module<T: Config> {
			Something
		}
	}

	frame_support::decl_storage! {
		trait Store for Module<T: Config> as Module {}
	}
}

mod nested {
	use super::*;

	pub mod module3 {
		use super::*;

		pub trait Config: system::Config {}

		frame_support::decl_module! {
			pub struct Module<T: Config> for enum Call
				where origin: <T as system::Config>::Origin, system=system
			{
				#[weight = 0]
				pub fn fail(_origin) -> frame_support::dispatch::DispatchResult {
					Err(Error::<T>::Something.into())
				}

				fn integrity_test() {
					INTEGRITY_TEST_EXEC.with(|i| *i.borrow_mut() += 1);
				}
			}
		}

		#[derive(Clone, PartialEq, Eq, Debug, codec::Encode, codec::Decode)]
		pub struct Origin;

		frame_support::decl_event! {
			pub enum Event {
				A,
			}
		}

		frame_support::decl_error! {
			pub enum Error for Module<T: Config> {
				Something
			}
		}

		frame_support::decl_storage! {
			trait Store for Module<T: Config> as Module {}
			add_extra_genesis {
				build(|_config| {})
			}
		}
	}
}

pub mod module3 {
	use super::*;

	pub trait Config: system::Config {}

	frame_support::decl_module! {
		pub struct Module<T: Config> for enum Call
			where origin: <T as system::Config>::Origin, system=system
		{
			#[weight = 0]
			pub fn fail(_origin) -> frame_support::dispatch::DispatchResult {
				Err(Error::<T>::Something.into())
			}
			#[weight = 0]
			pub fn aux_1(_origin, #[compact] _data: u32) -> frame_support::dispatch::DispatchResult {
				unreachable!()
			}
			#[weight = 0]
			pub fn aux_2(_origin, _data: i32, #[compact] _data2: u32) -> frame_support::dispatch::DispatchResult {
				unreachable!()
			}
			#[weight = 0]
			fn aux_3(_origin, _data: i32, _data2: String) -> frame_support::dispatch::DispatchResult {
				unreachable!()
			}
			#[weight = 3]
			fn aux_4(_origin) -> frame_support::dispatch::DispatchResult { unreachable!() }
			#[weight = (5, frame_support::weights::DispatchClass::Operational)]
			fn operational(_origin) { unreachable!() }
		}
	}

	#[derive(Clone, PartialEq, Eq, Debug, codec::Encode, codec::Decode)]
	pub struct Origin<T>(pub core::marker::PhantomData<T>);

	frame_support::decl_event! {
		pub enum Event {
			A,
		}
	}

	frame_support::decl_error! {
		pub enum Error for Module<T: Config> {
			Something
		}
	}

	frame_support::decl_storage! {
		trait Store for Module<T: Config> as Module {}
		add_extra_genesis {
			build(|_config| {})
		}
	}
}

impl<I> module1::Config<I> for Runtime {}
impl module2::Config for Runtime {}
impl nested::module3::Config for Runtime {}
impl module3::Config for Runtime {}

pub type Signature = sr25519::Signature;
pub type AccountId = <Signature as Verify>::Signer;
pub type BlockNumber = u64;
pub type Index = u64;

impl system::Config for Runtime {
	type BaseCallFilter = frame_support::traits::Everything;
	type Hash = H256;
	type Origin = Origin;
	type BlockNumber = BlockNumber;
	type AccountId = AccountId;
	type Event = Event;
	type PalletInfo = PalletInfo;
	type Call = Call;
	type DbWeight = ();
}

frame_support::construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{Pallet, Call, Event<T>, Origin<T>} = 30,
		Module1_1: module1::<Instance1>::{Pallet, Call, Storage, Event<T>, Origin<T>},
		Module2: module2::{Pallet, Call, Storage, Event, Origin},
		Module1_2: module1::<Instance2>::{Pallet, Call, Storage, Event<T>, Origin<T>},
		NestedModule3: nested::module3::{Pallet, Call, Config, Storage, Event, Origin},
		Module3: self::module3::{Pallet, Call, Config, Storage, Event, Origin<T>},
		Module1_3: module1::<Instance3>::{Pallet, Storage} = 6,
		Module1_4: module1::<Instance4>::{Pallet, Call} = 3,
		Module1_5: module1::<Instance5>::{Pallet, Event<T>},
		Module1_6: module1::<Instance6>::{Pallet, Call, Storage, Event<T>, Origin<T>} = 1,
		Module1_7: module1::<Instance7>::{Pallet, Call, Storage, Event<T>, Origin<T>},
		Module1_8: module1::<Instance8>::{Pallet, Call, Storage, Event<T>, Origin<T>} = 12,
		Module1_9: module1::<Instance9>::{Pallet, Call, Storage, Event<T>, Origin<T>},
	}
);

pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<u32, Call, Signature, ()>;

mod origin_test {
	use super::{module3, nested, system, Block, UncheckedExtrinsic};
	use frame_support::traits::{Contains, OriginTrait};

	impl nested::module3::Config for RuntimeOriginTest {}
	impl module3::Config for RuntimeOriginTest {}

	pub struct BaseCallFilter;
	impl Contains<Call> for BaseCallFilter {
		fn contains(c: &Call) -> bool {
			match c {
				Call::NestedModule3(_) => true,
				_ => false,
			}
		}
	}

	impl system::Config for RuntimeOriginTest {
		type BaseCallFilter = BaseCallFilter;
		type Hash = super::H256;
		type Origin = Origin;
		type BlockNumber = super::BlockNumber;
		type AccountId = u32;
		type Event = Event;
		type PalletInfo = PalletInfo;
		type Call = Call;
		type DbWeight = ();
	}

	frame_support::construct_runtime!(
		pub enum RuntimeOriginTest where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic
		{
			System: system::{Pallet, Event<T>, Origin<T>},
			NestedModule3: nested::module3::{Pallet, Origin, Call},
			Module3: module3::{Pallet, Origin<T>, Call},
		}
	);

	#[test]
	fn origin_default_filter() {
		let accepted_call = nested::module3::Call::fail().into();
		let rejected_call = module3::Call::fail().into();

		assert_eq!(Origin::root().filter_call(&accepted_call), true);
		assert_eq!(Origin::root().filter_call(&rejected_call), true);
		assert_eq!(Origin::none().filter_call(&accepted_call), true);
		assert_eq!(Origin::none().filter_call(&rejected_call), false);
		assert_eq!(Origin::signed(0).filter_call(&accepted_call), true);
		assert_eq!(Origin::signed(0).filter_call(&rejected_call), false);
		assert_eq!(Origin::from(Some(0)).filter_call(&accepted_call), true);
		assert_eq!(Origin::from(Some(0)).filter_call(&rejected_call), false);
		assert_eq!(Origin::from(None).filter_call(&accepted_call), true);
		assert_eq!(Origin::from(None).filter_call(&rejected_call), false);
		assert_eq!(Origin::from(super::nested::module3::Origin).filter_call(&accepted_call), true);
		assert_eq!(Origin::from(super::nested::module3::Origin).filter_call(&rejected_call), false);

		let mut origin = Origin::from(Some(0));

		origin.add_filter(|c| matches!(c, Call::Module3(_)));
		assert_eq!(origin.filter_call(&accepted_call), false);
		assert_eq!(origin.filter_call(&rejected_call), false);

		origin.set_caller_from(Origin::root());
		assert!(matches!(origin.caller, OriginCaller::system(super::system::RawOrigin::Root)));
		assert_eq!(origin.filter_call(&accepted_call), false);
		assert_eq!(origin.filter_call(&rejected_call), false);

		origin.reset_filter();
		assert_eq!(origin.filter_call(&accepted_call), true);
		assert_eq!(origin.filter_call(&rejected_call), false);
	}
}

#[test]
fn check_modules_error_type() {
	assert_eq!(
		Module1_1::fail(system::Origin::<Runtime>::Root.into()),
		Err(DispatchError::Module { index: 31, error: 0, message: Some("Something") }),
	);
	assert_eq!(
		Module2::fail(system::Origin::<Runtime>::Root.into()),
		Err(DispatchError::Module { index: 32, error: 0, message: Some("Something") }),
	);
	assert_eq!(
		Module1_2::fail(system::Origin::<Runtime>::Root.into()),
		Err(DispatchError::Module { index: 33, error: 0, message: Some("Something") }),
	);
	assert_eq!(
		NestedModule3::fail(system::Origin::<Runtime>::Root.into()),
		Err(DispatchError::Module { index: 34, error: 0, message: Some("Something") }),
	);
	assert_eq!(
		Module1_3::fail(system::Origin::<Runtime>::Root.into()),
		Err(DispatchError::Module { index: 6, error: 0, message: Some("Something") }),
	);
	assert_eq!(
		Module1_4::fail(system::Origin::<Runtime>::Root.into()),
		Err(DispatchError::Module { index: 3, error: 0, message: Some("Something") }),
	);
	assert_eq!(
		Module1_5::fail(system::Origin::<Runtime>::Root.into()),
		Err(DispatchError::Module { index: 4, error: 0, message: Some("Something") }),
	);
	assert_eq!(
		Module1_6::fail(system::Origin::<Runtime>::Root.into()),
		Err(DispatchError::Module { index: 1, error: 0, message: Some("Something") }),
	);
	assert_eq!(
		Module1_7::fail(system::Origin::<Runtime>::Root.into()),
		Err(DispatchError::Module { index: 2, error: 0, message: Some("Something") }),
	);
	assert_eq!(
		Module1_8::fail(system::Origin::<Runtime>::Root.into()),
		Err(DispatchError::Module { index: 12, error: 0, message: Some("Something") }),
	);
	assert_eq!(
		Module1_9::fail(system::Origin::<Runtime>::Root.into()),
		Err(DispatchError::Module { index: 13, error: 0, message: Some("Something") }),
	);
}

#[test]
fn integrity_test_works() {
	__construct_runtime_integrity_test::runtime_integrity_tests();
	assert_eq!(INTEGRITY_TEST_EXEC.with(|i| *i.borrow()), 2);
}

#[test]
fn origin_codec() {
	use codec::Encode;

	let origin = OriginCaller::system(system::RawOrigin::None);
	assert_eq!(origin.encode()[0], 30);

	let origin = OriginCaller::Module1_1(module1::Origin(Default::default()));
	assert_eq!(origin.encode()[0], 31);

	let origin = OriginCaller::Module2(module2::Origin);
	assert_eq!(origin.encode()[0], 32);

	let origin = OriginCaller::Module1_2(module1::Origin(Default::default()));
	assert_eq!(origin.encode()[0], 33);

	let origin = OriginCaller::NestedModule3(nested::module3::Origin);
	assert_eq!(origin.encode()[0], 34);

	let origin = OriginCaller::Module3(module3::Origin(Default::default()));
	assert_eq!(origin.encode()[0], 35);

	let origin = OriginCaller::Module1_6(module1::Origin(Default::default()));
	assert_eq!(origin.encode()[0], 1);

	let origin = OriginCaller::Module1_7(module1::Origin(Default::default()));
	assert_eq!(origin.encode()[0], 2);

	let origin = OriginCaller::Module1_8(module1::Origin(Default::default()));
	assert_eq!(origin.encode()[0], 12);

	let origin = OriginCaller::Module1_9(module1::Origin(Default::default()));
	assert_eq!(origin.encode()[0], 13);
}

#[test]
fn event_codec() {
	use codec::Encode;

	let event = system::Event::<Runtime>::ExtrinsicSuccess;
	assert_eq!(Event::from(event).encode()[0], 30);

	let event = module1::Event::<Runtime, module1::Instance1>::A(Default::default());
	assert_eq!(Event::from(event).encode()[0], 31);

	let event = module2::Event::A;
	assert_eq!(Event::from(event).encode()[0], 32);

	let event = module1::Event::<Runtime, module1::Instance2>::A(Default::default());
	assert_eq!(Event::from(event).encode()[0], 33);

	let event = nested::module3::Event::A;
	assert_eq!(Event::from(event).encode()[0], 34);

	let event = module3::Event::A;
	assert_eq!(Event::from(event).encode()[0], 35);

	let event = module1::Event::<Runtime, module1::Instance5>::A(Default::default());
	assert_eq!(Event::from(event).encode()[0], 4);

	let event = module1::Event::<Runtime, module1::Instance6>::A(Default::default());
	assert_eq!(Event::from(event).encode()[0], 1);

	let event = module1::Event::<Runtime, module1::Instance7>::A(Default::default());
	assert_eq!(Event::from(event).encode()[0], 2);

	let event = module1::Event::<Runtime, module1::Instance8>::A(Default::default());
	assert_eq!(Event::from(event).encode()[0], 12);

	let event = module1::Event::<Runtime, module1::Instance9>::A(Default::default());
	assert_eq!(Event::from(event).encode()[0], 13);
}

#[test]
fn call_codec() {
	use codec::Encode;
	assert_eq!(Call::System(system::Call::noop()).encode()[0], 30);
	assert_eq!(Call::Module1_1(module1::Call::fail()).encode()[0], 31);
	assert_eq!(Call::Module2(module2::Call::fail()).encode()[0], 32);
	assert_eq!(Call::Module1_2(module1::Call::fail()).encode()[0], 33);
	assert_eq!(Call::NestedModule3(nested::module3::Call::fail()).encode()[0], 34);
	assert_eq!(Call::Module3(module3::Call::fail()).encode()[0], 35);
	assert_eq!(Call::Module1_4(module1::Call::fail()).encode()[0], 3);
	assert_eq!(Call::Module1_6(module1::Call::fail()).encode()[0], 1);
	assert_eq!(Call::Module1_7(module1::Call::fail()).encode()[0], 2);
	assert_eq!(Call::Module1_8(module1::Call::fail()).encode()[0], 12);
	assert_eq!(Call::Module1_9(module1::Call::fail()).encode()[0], 13);
}

#[test]
fn call_compact_attr() {
	use codec::Encode;
	let call: module3::Call<Runtime> = module3::Call::aux_1(1);
	let encoded = call.encode();
	assert_eq!(2, encoded.len());
	assert_eq!(vec![1, 4], encoded);

	let call: module3::Call<Runtime> = module3::Call::aux_2(1, 2);
	let encoded = call.encode();
	assert_eq!(6, encoded.len());
	assert_eq!(vec![2, 1, 0, 0, 0, 8], encoded);
}

#[test]
fn call_encode_is_correct_and_decode_works() {
	use codec::{Decode, Encode};
	let call: module3::Call<Runtime> = module3::Call::fail();
	let encoded = call.encode();
	assert_eq!(vec![0], encoded);
	let decoded = module3::Call::<Runtime>::decode(&mut &encoded[..]).unwrap();
	assert_eq!(decoded, call);

	let call: module3::Call<Runtime> = module3::Call::aux_3(32, "hello".into());
	let encoded = call.encode();
	assert_eq!(vec![3, 32, 0, 0, 0, 20, 104, 101, 108, 108, 111], encoded);
	let decoded = module3::Call::<Runtime>::decode(&mut &encoded[..]).unwrap();
	assert_eq!(decoded, call);
}

#[test]
fn call_weight_should_attach_to_call_enum() {
	use frame_support::{
		dispatch::{DispatchInfo, GetDispatchInfo},
		weights::{DispatchClass, Pays},
	};
	// operational.
	assert_eq!(
		module3::Call::<Runtime>::operational().get_dispatch_info(),
		DispatchInfo { weight: 5, class: DispatchClass::Operational, pays_fee: Pays::Yes },
	);
	// custom basic
	assert_eq!(
		module3::Call::<Runtime>::aux_4().get_dispatch_info(),
		DispatchInfo { weight: 3, class: DispatchClass::Normal, pays_fee: Pays::Yes },
	);
}

#[test]
fn call_name() {
	use frame_support::dispatch::GetCallName;
	let name = module3::Call::<Runtime>::aux_4().get_call_name();
	assert_eq!("aux_4", name);
}

#[test]
fn call_metadata() {
	use frame_support::dispatch::{CallMetadata, GetCallMetadata};
	let call = Call::Module3(module3::Call::<Runtime>::aux_4());
	let metadata = call.get_call_metadata();
	let expected = CallMetadata { function_name: "aux_4".into(), pallet_name: "Module3".into() };
	assert_eq!(metadata, expected);
}

#[test]
fn get_call_names() {
	use frame_support::dispatch::GetCallName;
	let call_names = module3::Call::<Runtime>::get_call_names();
	assert_eq!(["fail", "aux_1", "aux_2", "aux_3", "aux_4", "operational"], call_names);
}

#[test]
fn get_module_names() {
	use frame_support::dispatch::GetCallMetadata;
	let module_names = Call::get_module_names();
	assert_eq!(
		[
			"System",
			"Module1_1",
			"Module2",
			"Module1_2",
			"NestedModule3",
			"Module3",
			"Module1_4",
			"Module1_6",
			"Module1_7",
			"Module1_8",
			"Module1_9",
		],
		module_names
	);
}

#[test]
fn call_subtype_conversion() {
	use frame_support::{dispatch::CallableCallFor, traits::IsSubType};
	let call = Call::Module3(module3::Call::<Runtime>::fail());
	let subcall: Option<&CallableCallFor<Module3, Runtime>> = call.is_sub_type();
	let subcall_none: Option<&CallableCallFor<Module2, Runtime>> = call.is_sub_type();
	assert_eq!(Some(&module3::Call::<Runtime>::fail()), subcall);
	assert_eq!(None, subcall_none);

	let from = Call::from(subcall.unwrap().clone());
	assert_eq!(from, call);
}

#[test]
fn test_metadata() {
	use frame_metadata::*;
	let expected_metadata: RuntimeMetadataLastVersion = RuntimeMetadataLastVersion {
		modules: DecodeDifferent::Encode(&[
			ModuleMetadata {
				name: DecodeDifferent::Encode("System"),
				storage: None,
				calls: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[FunctionMetadata {
						name: DecodeDifferent::Encode("noop"),
						arguments: DecodeDifferent::Encode(&[]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				event: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[
						EventMetadata {
							name: DecodeDifferent::Encode("ExtrinsicSuccess"),
							arguments: DecodeDifferent::Encode(&[]),
							documentation: DecodeDifferent::Encode(&[]),
						},
						EventMetadata {
							name: DecodeDifferent::Encode("ExtrinsicFailed"),
							arguments: DecodeDifferent::Encode(&[]),
							documentation: DecodeDifferent::Encode(&[]),
						},
						EventMetadata {
							name: DecodeDifferent::Encode("Ignore"),
							arguments: DecodeDifferent::Encode(&["BlockNumber"]),
							documentation: DecodeDifferent::Encode(&[]),
						},
					]
				}))),
				constants: DecodeDifferent::Encode(FnEncode(|| &[])),
				errors: DecodeDifferent::Encode(FnEncode(|| &[])),
				index: 30,
			},
			ModuleMetadata {
				name: DecodeDifferent::Encode("Module1_1"),
				storage: Some(DecodeDifferent::Encode(FnEncode(|| StorageMetadata {
					prefix: DecodeDifferent::Encode("Instance1Module"),
					entries: DecodeDifferent::Encode(&[]),
				}))),
				calls: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[FunctionMetadata {
						name: DecodeDifferent::Encode("fail"),
						arguments: DecodeDifferent::Encode(&[]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				event: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[EventMetadata {
						name: DecodeDifferent::Encode("A"),
						arguments: DecodeDifferent::Encode(&["AccountId"]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				constants: DecodeDifferent::Encode(FnEncode(|| &[])),
				errors: DecodeDifferent::Encode(FnEncode(|| &[])),
				index: 31,
			},
			ModuleMetadata {
				name: DecodeDifferent::Encode("Module2"),
				storage: Some(DecodeDifferent::Encode(FnEncode(|| StorageMetadata {
					prefix: DecodeDifferent::Encode("Module"),
					entries: DecodeDifferent::Encode(&[]),
				}))),
				calls: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[FunctionMetadata {
						name: DecodeDifferent::Encode("fail"),
						arguments: DecodeDifferent::Encode(&[]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				event: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[EventMetadata {
						name: DecodeDifferent::Encode("A"),
						arguments: DecodeDifferent::Encode(&[]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				constants: DecodeDifferent::Encode(FnEncode(|| &[])),
				errors: DecodeDifferent::Encode(FnEncode(|| &[])),
				index: 32,
			},
			ModuleMetadata {
				name: DecodeDifferent::Encode("Module1_2"),
				storage: Some(DecodeDifferent::Encode(FnEncode(|| StorageMetadata {
					prefix: DecodeDifferent::Encode("Instance2Module"),
					entries: DecodeDifferent::Encode(&[]),
				}))),
				calls: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[FunctionMetadata {
						name: DecodeDifferent::Encode("fail"),
						arguments: DecodeDifferent::Encode(&[]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				event: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[EventMetadata {
						name: DecodeDifferent::Encode("A"),
						arguments: DecodeDifferent::Encode(&["AccountId"]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				constants: DecodeDifferent::Encode(FnEncode(|| &[])),
				errors: DecodeDifferent::Encode(FnEncode(|| &[])),
				index: 33,
			},
			ModuleMetadata {
				name: DecodeDifferent::Encode("NestedModule3"),
				storage: Some(DecodeDifferent::Encode(FnEncode(|| StorageMetadata {
					prefix: DecodeDifferent::Encode("Module"),
					entries: DecodeDifferent::Encode(&[]),
				}))),
				calls: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[FunctionMetadata {
						name: DecodeDifferent::Encode("fail"),
						arguments: DecodeDifferent::Encode(&[]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				event: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[EventMetadata {
						name: DecodeDifferent::Encode("A"),
						arguments: DecodeDifferent::Encode(&[]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				constants: DecodeDifferent::Encode(FnEncode(|| &[])),
				errors: DecodeDifferent::Encode(FnEncode(|| &[])),
				index: 34,
			},
			ModuleMetadata {
				name: DecodeDifferent::Encode("Module3"),
				storage: Some(DecodeDifferent::Encode(FnEncode(|| StorageMetadata {
					prefix: DecodeDifferent::Encode("Module"),
					entries: DecodeDifferent::Encode(&[]),
				}))),
				calls: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[
						FunctionMetadata {
							name: DecodeDifferent::Encode("fail"),
							arguments: DecodeDifferent::Encode(&[]),
							documentation: DecodeDifferent::Encode(&[]),
						},
						FunctionMetadata {
							name: DecodeDifferent::Encode("aux_1"),
							arguments: DecodeDifferent::Encode(&[FunctionArgumentMetadata {
								name: DecodeDifferent::Encode("_data"),
								ty: DecodeDifferent::Encode("Compact<u32>"),
							}]),
							documentation: DecodeDifferent::Encode(&[]),
						},
						FunctionMetadata {
							name: DecodeDifferent::Encode("aux_2"),
							arguments: DecodeDifferent::Encode(&[
								FunctionArgumentMetadata {
									name: DecodeDifferent::Encode("_data"),
									ty: DecodeDifferent::Encode("i32"),
								},
								FunctionArgumentMetadata {
									name: DecodeDifferent::Encode("_data2"),
									ty: DecodeDifferent::Encode("Compact<u32>"),
								},
							]),
							documentation: DecodeDifferent::Encode(&[]),
						},
						FunctionMetadata {
							name: DecodeDifferent::Encode("aux_3"),
							arguments: DecodeDifferent::Encode(&[
								FunctionArgumentMetadata {
									name: DecodeDifferent::Encode("_data"),
									ty: DecodeDifferent::Encode("i32"),
								},
								FunctionArgumentMetadata {
									name: DecodeDifferent::Encode("_data2"),
									ty: DecodeDifferent::Encode("String"),
								},
							]),
							documentation: DecodeDifferent::Encode(&[]),
						},
						FunctionMetadata {
							name: DecodeDifferent::Encode("aux_4"),
							arguments: DecodeDifferent::Encode(&[]),
							documentation: DecodeDifferent::Encode(&[]),
						},
						FunctionMetadata {
							name: DecodeDifferent::Encode("operational"),
							arguments: DecodeDifferent::Encode(&[]),
							documentation: DecodeDifferent::Encode(&[]),
						},
					]
				}))),
				event: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[EventMetadata {
						name: DecodeDifferent::Encode("A"),
						arguments: DecodeDifferent::Encode(&[]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				constants: DecodeDifferent::Encode(FnEncode(|| &[])),
				errors: DecodeDifferent::Encode(FnEncode(|| &[])),
				index: 35,
			},
			ModuleMetadata {
				name: DecodeDifferent::Encode("Module1_3"),
				storage: Some(DecodeDifferent::Encode(FnEncode(|| StorageMetadata {
					prefix: DecodeDifferent::Encode("Instance3Module"),
					entries: DecodeDifferent::Encode(&[]),
				}))),
				calls: None,
				event: None,
				constants: DecodeDifferent::Encode(FnEncode(|| &[])),
				errors: DecodeDifferent::Encode(FnEncode(|| &[])),
				index: 6,
			},
			ModuleMetadata {
				name: DecodeDifferent::Encode("Module1_4"),
				storage: None,
				calls: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[FunctionMetadata {
						name: DecodeDifferent::Encode("fail"),
						arguments: DecodeDifferent::Encode(&[]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				event: None,
				constants: DecodeDifferent::Encode(FnEncode(|| &[])),
				errors: DecodeDifferent::Encode(FnEncode(|| &[])),
				index: 3,
			},
			ModuleMetadata {
				name: DecodeDifferent::Encode("Module1_5"),
				storage: None,
				calls: None,
				event: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[EventMetadata {
						name: DecodeDifferent::Encode("A"),
						arguments: DecodeDifferent::Encode(&["AccountId"]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				constants: DecodeDifferent::Encode(FnEncode(|| &[])),
				errors: DecodeDifferent::Encode(FnEncode(|| &[])),
				index: 4,
			},
			ModuleMetadata {
				name: DecodeDifferent::Encode("Module1_6"),
				storage: Some(DecodeDifferent::Encode(FnEncode(|| StorageMetadata {
					prefix: DecodeDifferent::Encode("Instance6Module"),
					entries: DecodeDifferent::Encode(&[]),
				}))),
				calls: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[FunctionMetadata {
						name: DecodeDifferent::Encode("fail"),
						arguments: DecodeDifferent::Encode(&[]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				event: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[EventMetadata {
						name: DecodeDifferent::Encode("A"),
						arguments: DecodeDifferent::Encode(&["AccountId"]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				constants: DecodeDifferent::Encode(FnEncode(|| &[])),
				errors: DecodeDifferent::Encode(FnEncode(|| &[])),
				index: 1,
			},
			ModuleMetadata {
				name: DecodeDifferent::Encode("Module1_7"),
				storage: Some(DecodeDifferent::Encode(FnEncode(|| StorageMetadata {
					prefix: DecodeDifferent::Encode("Instance7Module"),
					entries: DecodeDifferent::Encode(&[]),
				}))),
				calls: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[FunctionMetadata {
						name: DecodeDifferent::Encode("fail"),
						arguments: DecodeDifferent::Encode(&[]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				event: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[EventMetadata {
						name: DecodeDifferent::Encode("A"),
						arguments: DecodeDifferent::Encode(&["AccountId"]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				constants: DecodeDifferent::Encode(FnEncode(|| &[])),
				errors: DecodeDifferent::Encode(FnEncode(|| &[])),
				index: 2,
			},
			ModuleMetadata {
				name: DecodeDifferent::Encode("Module1_8"),
				storage: Some(DecodeDifferent::Encode(FnEncode(|| StorageMetadata {
					prefix: DecodeDifferent::Encode("Instance8Module"),
					entries: DecodeDifferent::Encode(&[]),
				}))),
				calls: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[FunctionMetadata {
						name: DecodeDifferent::Encode("fail"),
						arguments: DecodeDifferent::Encode(&[]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				event: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[EventMetadata {
						name: DecodeDifferent::Encode("A"),
						arguments: DecodeDifferent::Encode(&["AccountId"]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				constants: DecodeDifferent::Encode(FnEncode(|| &[])),
				errors: DecodeDifferent::Encode(FnEncode(|| &[])),
				index: 12,
			},
			ModuleMetadata {
				name: DecodeDifferent::Encode("Module1_9"),
				storage: Some(DecodeDifferent::Encode(FnEncode(|| StorageMetadata {
					prefix: DecodeDifferent::Encode("Instance9Module"),
					entries: DecodeDifferent::Encode(&[]),
				}))),
				calls: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[FunctionMetadata {
						name: DecodeDifferent::Encode("fail"),
						arguments: DecodeDifferent::Encode(&[]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				event: Some(DecodeDifferent::Encode(FnEncode(|| {
					&[EventMetadata {
						name: DecodeDifferent::Encode("A"),
						arguments: DecodeDifferent::Encode(&["AccountId"]),
						documentation: DecodeDifferent::Encode(&[]),
					}]
				}))),
				constants: DecodeDifferent::Encode(FnEncode(|| &[])),
				errors: DecodeDifferent::Encode(FnEncode(|| &[])),
				index: 13,
			},
		]),
		extrinsic: ExtrinsicMetadata {
			version: 4,
			signed_extensions: vec![DecodeDifferent::Encode("UnitSignedExtension")],
		},
	};
	pretty_assertions::assert_eq!(Runtime::metadata().1, RuntimeMetadata::V13(expected_metadata));
}

#[test]
fn pallet_in_runtime_is_correct() {
	assert_eq!(PalletInfo::index::<System>().unwrap(), 30);
	assert_eq!(PalletInfo::name::<System>().unwrap(), "System");

	assert_eq!(PalletInfo::index::<Module1_1>().unwrap(), 31);
	assert_eq!(PalletInfo::name::<Module1_1>().unwrap(), "Module1_1");

	assert_eq!(PalletInfo::index::<Module2>().unwrap(), 32);
	assert_eq!(PalletInfo::name::<Module2>().unwrap(), "Module2");

	assert_eq!(PalletInfo::index::<Module1_2>().unwrap(), 33);
	assert_eq!(PalletInfo::name::<Module1_2>().unwrap(), "Module1_2");

	assert_eq!(PalletInfo::index::<NestedModule3>().unwrap(), 34);
	assert_eq!(PalletInfo::name::<NestedModule3>().unwrap(), "NestedModule3");

	assert_eq!(PalletInfo::index::<Module3>().unwrap(), 35);
	assert_eq!(PalletInfo::name::<Module3>().unwrap(), "Module3");

	assert_eq!(PalletInfo::index::<Module1_3>().unwrap(), 6);
	assert_eq!(PalletInfo::name::<Module1_3>().unwrap(), "Module1_3");

	assert_eq!(PalletInfo::index::<Module1_4>().unwrap(), 3);
	assert_eq!(PalletInfo::name::<Module1_4>().unwrap(), "Module1_4");

	assert_eq!(PalletInfo::index::<Module1_5>().unwrap(), 4);
	assert_eq!(PalletInfo::name::<Module1_5>().unwrap(), "Module1_5");

	assert_eq!(PalletInfo::index::<Module1_6>().unwrap(), 1);
	assert_eq!(PalletInfo::name::<Module1_6>().unwrap(), "Module1_6");

	assert_eq!(PalletInfo::index::<Module1_7>().unwrap(), 2);
	assert_eq!(PalletInfo::name::<Module1_7>().unwrap(), "Module1_7");

	assert_eq!(PalletInfo::index::<Module1_8>().unwrap(), 12);
	assert_eq!(PalletInfo::name::<Module1_8>().unwrap(), "Module1_8");

	assert_eq!(PalletInfo::index::<Module1_9>().unwrap(), 13);
	assert_eq!(PalletInfo::name::<Module1_9>().unwrap(), "Module1_9");
}
