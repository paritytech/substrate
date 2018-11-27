// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

// tag::description[]
//! Support code for the runtime.
// end::description[]

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]

#[cfg(feature = "std")]
extern crate serde;

#[macro_use]
extern crate srml_support;
#[macro_use]
extern crate srml_support_procedural;
#[doc(hidden)]
pub extern crate sr_std as rstd;
extern crate sr_io as runtime_io;
#[doc(hidden)]
pub extern crate sr_primitives as runtime_primitives;
extern crate substrate_metadata;

extern crate mashup;

#[macro_use]
extern crate pretty_assertions;
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate parity_codec_derive;

#[doc(hidden)]
pub extern crate parity_codec as codec;

/*
mod ex1 { 
decl_storage! {
	trait Store for Module<T: Trait> as UpgradeKey {
		Key get(key) config(): T::AccountId;
	}
}
}
*/
mod ex2 {

	use super::*;
	use substrate_metadata::{
		EventMetadata, OuterEventMetadata, RuntimeModuleMetadata, CallMetadata, ModuleMetadata,
		StorageFunctionModifier, StorageFunctionType, FunctionMetadata,
		StorageMetadata, StorageFunctionMetadata, OuterDispatchMetadata, OuterDispatchCall
	};
	use codec::{Decode, Encode};

	mod system {
		pub trait Trait {
			type Origin: Into<Option<RawOrigin<Self::AccountId>>> + From<RawOrigin<Self::AccountId>>;
			type AccountId;
			type BlockNumber;
		}

		decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
		}

		decl_event!(
			pub enum Event {
				SystemEvent,
			}
		);

		#[derive(Clone, PartialEq, Eq, Debug)]
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
	}

	mod event_module {
		use dispatch::Result;

		pub trait Trait {
			type Origin;
			type Balance;
			type BlockNumber;
		}

		decl_event!(
			pub enum Event<T> where <T as Trait>::Balance
			{
				/// Hi, I am a comment.
				TestEvent(Balance),
			}
		);

		decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin {
				fn aux_0(_origin) -> Result { unreachable!() }
			}
		}
	}

	mod event_module2 {
		pub trait Trait {
			type Origin;
			type Balance;
			type BlockNumber;
		}

		decl_event!(
			pub enum Event<T> where <T as Trait>::Balance
			{
				TestEvent(Balance),
			}
		);

		decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
		}

		decl_storage! {
			trait Store for Module<T: Trait> as TestStorage {
				StorageMethod : Option<u32>;
			}
			add_extra_genesis {
			    config(_marker) : ::std::marker::PhantomData<T>;
			    build(|_, _| {});
			}
		}
	}

	type EventModule = event_module::Module<TestRuntime>;
	type EventModule2 = event_module2::Module<TestRuntime>;

	#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, Deserialize, Serialize)]
	pub struct TestRuntime;

	impl_outer_event! {
		pub enum TestEvent for TestRuntime {
			event_module<T>,
			event_module2<T>,
		}
	}

	impl_outer_origin! {
		pub enum Origin for TestRuntime {}
	}

	impl_outer_dispatch! {
		pub enum Call for TestRuntime where origin: Origin {
			event_module::EventModule,
			event_module2::EventModule2,
		}
	}

	impl event_module::Trait for TestRuntime {
		type Origin = Origin;
		type Balance = u32;
		type BlockNumber = u32;
	}

	impl event_module2::Trait for TestRuntime {
		type Origin = Origin;
		type Balance = u32;
		type BlockNumber = u32;
	}

	impl system::Trait for TestRuntime {
		type Origin = Origin;
		type AccountId = u32;
		type BlockNumber = u32;
	}

	impl_runtime_metadata!(
		for TestRuntime with modules
			event_module::Module,
			event_module2::Module with Storage,
	);

	const EXPECTED_METADATA: RuntimeMetadata = RuntimeMetadata {
		outer_event: OuterEventMetadata {
			name: DecodeDifferent::Encode("TestEvent"),
			events: DecodeDifferent::Encode(&[
				(
					"system",
					FnEncode(|| &[
						EventMetadata {
							name: DecodeDifferent::Encode("SystemEvent"),
							arguments: DecodeDifferent::Encode(&[]),
							documentation: DecodeDifferent::Encode(&[]),
						}
					])
				),
				(
					"event_module",
					FnEncode(|| &[
						EventMetadata {
							name: DecodeDifferent::Encode("TestEvent"),
							arguments: DecodeDifferent::Encode(&["Balance"]),
							documentation: DecodeDifferent::Encode(&[" Hi, I am a comment."])
						}
					])
				),
				(
					"event_module2",
					FnEncode(|| &[
						EventMetadata {
							name: DecodeDifferent::Encode("TestEvent"),
							arguments: DecodeDifferent::Encode(&["Balance"]),
							documentation: DecodeDifferent::Encode(&[])
						}
					])
				)
			]),
		},
		modules: DecodeDifferent::Encode(&[
			RuntimeModuleMetadata {
				prefix: DecodeDifferent::Encode("event_module"),
				module: DecodeDifferent::Encode(FnEncode(||
					ModuleMetadata {
					 name: DecodeDifferent::Encode("Module"),
					 call: CallMetadata {
						 name: DecodeDifferent::Encode("Call"),
						 functions: DecodeDifferent::Encode(&[
							 FunctionMetadata {
								 id: 0,
								 name: DecodeDifferent::Encode("aux_0"),
								 arguments: DecodeDifferent::Encode(&[]),
								 documentation: DecodeDifferent::Encode(&[]),
							 }
						 ])
					 }
					}
				)),
				storage: None,
			},
			RuntimeModuleMetadata {
				prefix: DecodeDifferent::Encode("event_module2"),
				module: DecodeDifferent::Encode(FnEncode(||
					ModuleMetadata {
					 name: DecodeDifferent::Encode("Module"),
					 call: CallMetadata {
						 name: DecodeDifferent::Encode("Call"),
						 functions: DecodeDifferent::Encode(&[])
					 }
					}
				)),
				storage: Some(DecodeDifferent::Encode(FnEncode(||
					StorageMetadata {
					   prefix: DecodeDifferent::Encode("TestStorage"),
					   functions: DecodeDifferent::Encode(&[
						   StorageFunctionMetadata {
							   name: DecodeDifferent::Encode("StorageMethod"),
							   modifier: StorageFunctionModifier::Optional,
							   ty: StorageFunctionType::Plain(DecodeDifferent::Encode("u32")),
							   documentation: DecodeDifferent::Encode(&[]),
						   }
					   ])
					}
				))),
			}
		]),
		outer_dispatch: OuterDispatchMetadata {
			name: DecodeDifferent::Encode("Call"),
			calls: DecodeDifferent::Encode(&[
				OuterDispatchCall {
					name: DecodeDifferent::Encode("EventModule"),
					prefix: DecodeDifferent::Encode("event_module"),
					index: 0,
				},
				OuterDispatchCall {
					name: DecodeDifferent::Encode("EventModule2"),
					prefix: DecodeDifferent::Encode("event_module2"),
					index: 1,
				}
			])
		}
	};

	#[test]
	fn runtime_metadata() {
		let metadata_encoded = TestRuntime::metadata().encode();
		let metadata_decoded = RuntimeMetadata::decode(&mut &metadata_encoded[..]);

		assert_eq!(EXPECTED_METADATA, metadata_decoded.unwrap());
	}
}
