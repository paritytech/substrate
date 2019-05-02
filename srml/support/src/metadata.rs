// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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
	ModuleMetadata, RuntimeMetadataV4,
	DefaultByteGetter, RuntimeMetadataPrefixed,
	StorageMetadata, StorageFunctionMetadata,
	StorageFunctionType, StorageFunctionModifier,
	DefaultByte, StorageHasher
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
				$crate::metadata::RuntimeMetadata::V4 (
					$crate::metadata::RuntimeMetadataV4 {
						modules: $crate::__runtime_modules_to_metadata!($runtime;; $( $rest )*),
					}
				).into()
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
		$mod:ident::$module:ident $( < $instance:ident > )? $(with)+ $($kw:ident)*,
		$( $rest:tt )*
	) => {
		$crate::__runtime_modules_to_metadata!(
			$runtime;
			$( $metadata, )* $crate::metadata::ModuleMetadata {
				name: $crate::metadata::DecodeDifferent::Encode(stringify!($mod)),
				prefix: $crate::__runtime_modules_to_metadata_calls_storagename!($mod, $module $( <$instance> )?, $runtime, $(with $kw)*),
				storage: $crate::__runtime_modules_to_metadata_calls_storage!($mod, $module $( <$instance> )?, $runtime, $(with $kw)*),
				calls: $crate::__runtime_modules_to_metadata_calls_call!($mod, $module $( <$instance> )?, $runtime, $(with $kw)*),
				event: $crate::__runtime_modules_to_metadata_calls_event!($mod, $module $( <$instance> )?, $runtime, $(with $kw)*),
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
	// skip system
	(
		system,
		$skip_module: ident $( <$instance:ident> )?,
		$skip_runtime: ident,
		with Call
		$(with $kws:ident)*
	) => {
		None
	};
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with Call
		$(with $kws:ident)*
	) => {
		Some($crate::metadata::DecodeDifferent::Encode(
			$crate::metadata::FnEncode(
				$mod::$module::<$runtime $(, $mod::$instance )?>::call_functions
			)
		))
	};
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with $_:ident
		$(with $kws:ident)*
	) => {
		$crate::__runtime_modules_to_metadata_calls_call!( $mod, $module $( <$instance> )?, $runtime, $(with $kws)* );
	};
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
	) => {
		None
	};
}


#[macro_export]
#[doc(hidden)]
macro_rules! __runtime_modules_to_metadata_calls_event {
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with Event
		$(with $kws:ident)*
	) => {
		Some($crate::metadata::DecodeDifferent::Encode(
			$crate::metadata::FnEncode(
				$crate::paste::expr!{
					$runtime:: [< __module_events_ $mod $(_ $instance)?>]
				}
			)
		))
	};
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with $_:ident
		$(with $kws:ident)*
	) => {
		$crate::__runtime_modules_to_metadata_calls_event!( $mod, $module $( <$instance> )?, $runtime, $(with $kws)* );
	};
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
	) => {
		None
	};
}

#[macro_export]
#[doc(hidden)]
macro_rules! __runtime_modules_to_metadata_calls_storagename {
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with Storage
		$(with $kws:ident)*
	) => {
		$crate::metadata::DecodeDifferent::Encode(
			$crate::metadata::FnEncode(
				$mod::$module::<$runtime $(, $mod::$instance )?>::store_metadata_name
			)
		)
	};
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with $_:ident
		$(with $kws:ident)*
	) => {
		$crate::__runtime_modules_to_metadata_calls_storagename!( $mod, $module $( <$instance> )?, $runtime, $(with $kws)* );
	};
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
	) => {
		$crate::metadata::DecodeDifferent::Encode(
			$crate::metadata::FnEncode(|| "")
		)
	};
}

#[macro_export]
#[doc(hidden)]
macro_rules! __runtime_modules_to_metadata_calls_storage {
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with Storage
		$(with $kws:ident)*
	) => {
		Some($crate::metadata::DecodeDifferent::Encode(
			$crate::metadata::FnEncode(
				$mod::$module::<$runtime $(, $mod::$instance )?>::store_metadata_functions
			)
		))
	};
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with $_:ident
		$(with $kws:ident)*
	) => {
		$crate::__runtime_modules_to_metadata_calls_storage!( $mod, $module $( <$instance> )?, $runtime, $(with $kws)* );
	};
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
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
		EventMetadata,
		StorageFunctionModifier, StorageFunctionType, FunctionMetadata,
		StorageFunctionMetadata,
		ModuleMetadata, RuntimeMetadataPrefixed
	};
	use crate::codec::{Encode, Decode};

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
	}

	mod event_module {
		use crate::dispatch::Result;

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

		crate::decl_storage! {
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

	const EXPECTED_METADATA: RuntimeMetadata = RuntimeMetadata::V4(
		RuntimeMetadataV4 {
		modules: DecodeDifferent::Encode(&[
			ModuleMetadata {
				name: DecodeDifferent::Encode("system"),
				prefix: DecodeDifferent::Encode(FnEncode(||"")),
				storage: None,
				calls: None,
				event: Some(DecodeDifferent::Encode(
			 		FnEncode(||&[
						EventMetadata {
							name: DecodeDifferent::Encode("SystemEvent"),
							arguments: DecodeDifferent::Encode(&[]),
							documentation: DecodeDifferent::Encode(&[])
						}
			 		])
				)),
			},
			ModuleMetadata {
				name: DecodeDifferent::Encode("event_module"),
				prefix: DecodeDifferent::Encode(FnEncode(||"")),
				storage: None,
				calls: Some(
					DecodeDifferent::Encode(FnEncode(||&[
						FunctionMetadata {
							name: DecodeDifferent::Encode("aux_0"),
							arguments: DecodeDifferent::Encode(&[]),
							documentation: DecodeDifferent::Encode(&[]),
						}
					]))),
				event: Some(DecodeDifferent::Encode(
			 		FnEncode(||&[
						EventMetadata {
							name: DecodeDifferent::Encode("TestEvent"),
							arguments: DecodeDifferent::Encode(&["Balance"]),
							documentation: DecodeDifferent::Encode(&[" Hi, I am a comment."])
						}
			 		])
				)),
			},
			ModuleMetadata {
				name: DecodeDifferent::Encode("event_module2"),
				prefix: DecodeDifferent::Encode(FnEncode(||"TestStorage")),
				storage: Some(DecodeDifferent::Encode(
			 		FnEncode(||&[
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
				)),
				calls: Some(DecodeDifferent::Encode(FnEncode(||&[	]))),
				event: Some(DecodeDifferent::Encode(
			 		FnEncode(||&[
						EventMetadata {
							name: DecodeDifferent::Encode("TestEvent"),
							arguments: DecodeDifferent::Encode(&["Balance"]),
							documentation: DecodeDifferent::Encode(&[])
						}
			 		])
				)),
			},
		])}
	);

	#[test]
	fn runtime_metadata() {
		let metadata_encoded = TestRuntime::metadata().encode();
		let metadata_decoded = RuntimeMetadataPrefixed::decode(&mut &metadata_encoded[..]);
		let expected_metadata: RuntimeMetadataPrefixed = EXPECTED_METADATA.into();

		assert_eq!(expected_metadata, metadata_decoded.unwrap());
	}
}
