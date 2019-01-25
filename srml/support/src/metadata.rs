// Copyright 2018 Parity Technologies (UK) Ltd.
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

pub use srml_metadata::{
	DecodeDifferent, FnEncode, RuntimeMetadata,
	RuntimeModuleMetadata, RuntimeMetadataV1,
	DefaultByteGetter, META_RESERVED, RuntimeMetadataPrefixed,
};

/// Implements the metadata support for the given runtime and all its modules.
///
/// Example:
/// ```compile_fail
/// impl_runtime_metadata!(for RUNTIME_NAME with modules MODULE0, MODULE2, MODULE3 with Storage);
/// ```
///
/// In this example, just `MODULE3` implements the `Storage` trait.
#[macro_export]
macro_rules! impl_runtime_metadata {
	(
		for $runtime:ident with modules
			$( $rest:tt )*
	) => {
		impl $runtime {
			pub fn metadata() -> $crate::metadata::RuntimeMetadataPrefixed {
				$crate::metadata::RuntimeMetadataPrefixed (
					$crate::metadata::META_RESERVED,
					$crate::metadata::RuntimeMetadata::V1 (
						$crate::metadata::RuntimeMetadataV1 {
							modules: __runtime_modules_to_metadata!($runtime;; $( $rest )*),
						}
					)
				)
			}
		}
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __runtime_modules_to_metadata {
	(
		$runtime: ident;
		$( $metadata:expr ),*;
		$mod:ident::$module:ident $(with)+ $($kw:ident)*,
		$( $rest:tt )*
	) => {
		__runtime_modules_to_metadata!(
			$runtime;
			$( $metadata, )* $crate::metadata::RuntimeModuleMetadata {
				name: $crate::metadata::DecodeDifferent::Encode(stringify!($module)),
				prefix: $crate::metadata::DecodeDifferent::Encode(stringify!($mod)),
				storage: __runtime_modules_to_metadata_calls_storage!($mod, $module, $runtime, $(with $kw)*),
				call: $crate::metadata::DecodeDifferent::Encode(
					$crate::metadata::FnEncode($mod::$module::<$runtime>::call_module)
				),
				outer_dispatch: $crate::metadata::DecodeDifferent::Encode(
					__runtime_modules_to_metadata_calls_call!($mod, $module, $runtime, $(with $kw)*)
				),
				event: $crate::metadata::DecodeDifferent::Encode(
					__runtime_modules_to_metadata_calls_event!($mod, $module, $runtime, $(with $kw)*)
				),
			};
			$( $rest )*
		)
	};
	(
		$runtime:ident;
		$( $metadata:expr ),*;
	) => {
		$crate::metadata::DecodeDifferent::Encode(&[ $( $metadata ),* ])
	};
}

#[macro_export]
#[doc(hidden)]
macro_rules! __runtime_modules_to_metadata_calls_call {
	(
		$mod: ident,
		$module: ident,
		$runtime: ident,
		with Call 
		$(with $kws:ident)*
	) => {
		$crate::metadata::FnEncode(
			$crate::paste::expr!{
				$runtime:: [< __module_dispatch_ $mod >]
			}
		)
	};
	(
		$mod: ident,
		$module: ident,
		$runtime: ident,
		with $_:ident 
		$(with $kws:ident)*
	) => {
		__runtime_modules_to_metadata_calls_call!( $mod, $module, $runtime, $(with $kws)* );
	};
	(
		$mod: ident,
		$module: ident,
		$runtime: ident,
	) => {
		$crate::metadata::FnEncode($runtime::__module_dispatch___default)
	};
}


#[macro_export]
#[doc(hidden)]
macro_rules! __runtime_modules_to_metadata_calls_event {
	(
		$mod: ident,
		$module: ident,
		$runtime: ident,
		with Event 
		$(with $kws:ident)*
	) => {
		$crate::metadata::FnEncode(
			$crate::paste::expr!{
				$runtime:: [< __module_events_ $mod >]
			}
		)
	};
	(
		$mod: ident,
		$module: ident,
		$runtime: ident,
		with $_:ident 
		$(with $kws:ident)*
	) => {
		__runtime_modules_to_metadata_calls_event!( $mod, $module, $runtime, $(with $kws)* );
	};
	(
		$mod: ident,
		$module: ident,
		$runtime: ident,
	) => {
		$crate::metadata::FnEncode($runtime::__module_events___default)
	};
}

#[macro_export]
#[doc(hidden)]
macro_rules! __runtime_modules_to_metadata_calls_storage {
	(
		$mod: ident,
		$module: ident,
		$runtime: ident,
		with Storage 
		$(with $kws:ident)*
	) => {
		Some($crate::metadata::DecodeDifferent::Encode(
			$crate::metadata::FnEncode($mod::$module::<$runtime>::store_metadata)
		))
	};
	(
		$mod: ident,
		$module: ident,
		$runtime: ident,
		with $_:ident 
		$(with $kws:ident)*
	) => {
		__runtime_modules_to_metadata_calls_storage!( $mod, $module, $runtime, $(with $kws)* );
	};
	(
		$mod: ident,
		$module: ident,
		$runtime: ident,
	) => {
		None
	};
}


#[cfg(test)]
// Do not complain about unused `dispatch` and `dispatch_aux`.
#[allow(dead_code)]
mod tests {
	use super::*;
	use srml_metadata::{
		EventMetadata, CallMetadata,
		StorageFunctionModifier, StorageFunctionType, FunctionMetadata,
		StorageMetadata, StorageFunctionMetadata, OuterDispatchCall,
		RuntimeModuleMetadata, RuntimeMetadataPrefixed,
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
				build(|_, _, _| {});
			}
		}
	}

	type EventModule = event_module::Module<TestRuntime>;
	type EventModule2 = event_module2::Module<TestRuntime>;

	#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode)]
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
			system::Module with Event,
			event_module::Module with Event Call,
			event_module2::Module with Event Storage Call,
	);

	const EXPECTED_METADATA: RuntimeMetadataPrefixed = RuntimeMetadataPrefixed (
		META_RESERVED,
		RuntimeMetadata::V1(
		RuntimeMetadataV1 {
		modules: DecodeDifferent::Encode(&[
			RuntimeModuleMetadata {
				name: DecodeDifferent::Encode("Module"),
				prefix: DecodeDifferent::Encode("system"),
				storage: None,
				// lost DecodeDifferent::Encode("Module"), aka module metadata name
				call: DecodeDifferent::Encode(FnEncode(||
					CallMetadata {
						name: DecodeDifferent::Encode("Call"),
						functions: DecodeDifferent::Encode(&[
						]),
				})),
				outer_dispatch: DecodeDifferent::Encode(
					FnEncode(|| None)
				),
				event: DecodeDifferent::Encode(
					FnEncode(||
				 		FnEncode(||&[
							EventMetadata {
								name: DecodeDifferent::Encode("SystemEvent"),
								arguments: DecodeDifferent::Encode(&[]),
								documentation: DecodeDifferent::Encode(&[])
							}
				 		])
					)
				),
			},
	
			RuntimeModuleMetadata {
				prefix: DecodeDifferent::Encode("event_module"),
				name: DecodeDifferent::Encode("Module"),
				storage: None,
				// lost DecodeDifferent::Encode("Module"), aka module metadata name
				call: DecodeDifferent::Encode(FnEncode(||
					CallMetadata {
						name: DecodeDifferent::Encode("Call"),
						functions: DecodeDifferent::Encode(&[
					 		FunctionMetadata {
						 		id: 0,
								name: DecodeDifferent::Encode("aux_0"),
								arguments: DecodeDifferent::Encode(&[]),
								documentation: DecodeDifferent::Encode(&[]),
							}
						]),
				})),
				outer_dispatch: DecodeDifferent::Encode(
					FnEncode(||
						Some(OuterDispatchCall {
							name: DecodeDifferent::Encode("EventModule"),
							index: 0,
						})
					)
				),
				event: DecodeDifferent::Encode(
					FnEncode(||
				 		FnEncode(||&[
							EventMetadata {
								name: DecodeDifferent::Encode("TestEvent"),
								arguments: DecodeDifferent::Encode(&["Balance"]),
								documentation: DecodeDifferent::Encode(&[" Hi, I am a comment."])
							}
				 		])
					)
				),
			},
			RuntimeModuleMetadata {
				prefix: DecodeDifferent::Encode("event_module2"),
				name: DecodeDifferent::Encode("Module"),
				storage: Some(DecodeDifferent::Encode(FnEncode(||
					StorageMetadata {
						prefix: DecodeDifferent::Encode("TestStorage"),
						functions: DecodeDifferent::Encode(&[
							StorageFunctionMetadata {
								name: DecodeDifferent::Encode("StorageMethod"),
								modifier: StorageFunctionModifier::Optional,
								ty: StorageFunctionType::Plain(DecodeDifferent::Encode("u32")),
								default: DecodeDifferent::Encode(
									DefaultByteGetter(
										&event_module2::__GetByteStructStorageMethod(::std::marker::PhantomData::<TestRuntime>)
									)
								),
								documentation: DecodeDifferent::Encode(&[]),
							}
						])
					}
				))),
				// lost DecodeDifferent::Encode("Module"), aka module metadata name
				call: DecodeDifferent::Encode(FnEncode(||
					CallMetadata {
						name: DecodeDifferent::Encode("Call"),
						functions: DecodeDifferent::Encode(&[]),
					}
				)),
				outer_dispatch: DecodeDifferent::Encode(
					FnEncode(||
						Some(OuterDispatchCall {
							name: DecodeDifferent::Encode("EventModule2"),
							index: 1,
						})
					)
				),
				event: DecodeDifferent::Encode(
					FnEncode(||
				 		FnEncode(||&[
							EventMetadata {
								name: DecodeDifferent::Encode("TestEvent"),
								arguments: DecodeDifferent::Encode(&["Balance"]),
								documentation: DecodeDifferent::Encode(&[])
							}
				 		])
					)
				),
			},
		])}),
	);

	#[test]
	fn runtime_metadata() {
		let metadata_encoded = TestRuntime::metadata().encode();
		let metadata_decoded = RuntimeMetadataPrefixed::decode(&mut &metadata_encoded[..]);

		assert_eq!(EXPECTED_METADATA, metadata_decoded.unwrap());
	}
}
