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
	ModuleMetadata, RuntimeMetadataV2,
	DefaultByteGetter, RuntimeMetadataPrefixed,
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
				let mut registry = $crate::substrate_metadata::MetadataRegistry::new();
				$crate::metadata::RuntimeMetadata::V2 (
					$crate::metadata::RuntimeMetadataV2 {
						modules: $crate::__runtime_modules_to_metadata!(registry; $runtime;; $( $rest )*),
						type_registry: registry
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
		$registry: ident;
		$runtime: ident;
		$( $metadata:expr ),*;
		$mod:ident::$module:ident $(with)+ $($kw:ident)*,
		$( $rest:tt )*
	) => {
		$crate::__runtime_modules_to_metadata!(
			$registry;
			$runtime;
			$( $metadata, )* $crate::metadata::ModuleMetadata {
				name: $crate::metadata::DecodeDifferent::Encode(stringify!($mod)),
				prefix: $crate::__runtime_modules_to_metadata_calls_storagename!($mod, $module, $runtime, $(with $kw)*),
				storage: $crate::__runtime_modules_to_metadata_calls_storage!($registry, $mod, $module, $runtime, $(with $kw)*),
				calls: $crate::__runtime_modules_to_metadata_calls_call!($registry, $mod, $module, $runtime, $(with $kw)*),
				event: $crate::__runtime_modules_to_metadata_calls_event!($mod, $module, $runtime, $(with $kw)*),
			};
			$( $rest )*
		)
	};
	(
		$registry: ident;
		$runtime:ident;
		$( $metadata:expr ),*;
	) => {
		vec![ $( $metadata ),* ]
	};
}

#[macro_export]
#[doc(hidden)]
macro_rules! __runtime_modules_to_metadata_calls_call {
	// skip system
	(
		$registry: ident,
		system,
		$skip_module: ident,
		$skip_runtime: ident,
		with Call
		$(with $kws:ident)*
	) => {
		None
	};
	(
		$registry: ident,
		$mod: ident,
		$module: ident,
		$runtime: ident,
		with Call
		$(with $kws:ident)*
	) => {
		{
			$mod::$module::<$runtime>::call_metadata_register(&mut $registry);
			Some($crate::metadata::DecodeDifferent::Encode(
				$crate::metadata::FnEncode(
					$mod::$module::<$runtime>::call_functions
				)
			))
		}
	};
	(
		$registry: ident,
		$mod: ident,
		$module: ident,
		$runtime: ident,
		with $_:ident
		$(with $kws:ident)*
	) => {
 		$crate::__runtime_modules_to_metadata_calls_call!( $registry, $mod, $module, $runtime, $(with $kws)* );
	};
	(
		$registry: ident,
		$mod: ident,
		$module: ident,
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
		$module: ident,
		$runtime: ident,
		with Event
		$(with $kws:ident)*
	) => {
		Some($crate::metadata::DecodeDifferent::Encode(
			$crate::metadata::FnEncode(
				$crate::paste::expr!{
					$runtime:: [< __module_events_ $mod >]
				}
			)
		))
	};
	(
		$mod: ident,
		$module: ident,
		$runtime: ident,
		with $_:ident
		$(with $kws:ident)*
	) => {
		$crate::__runtime_modules_to_metadata_calls_event!( $mod, $module, $runtime, $(with $kws)* );
	};
	(
		$mod: ident,
		$module: ident,
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
		$module: ident,
		$runtime: ident,
		with Storage
		$(with $kws:ident)*
	) => {
		$crate::metadata::DecodeDifferent::Encode(
			$crate::metadata::FnEncode(
				$mod::$module::<$runtime>::store_metadata_name
			)
		)
	};
	(
		$mod: ident,
		$module: ident,
		$runtime: ident,
		with $_:ident
		$(with $kws:ident)*
	) => {
		$crate::__runtime_modules_to_metadata_calls_storagename!( $mod, $module, $runtime, $(with $kws)* );
	};
	(
		$mod: ident,
		$module: ident,
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
		$registry: ident,
		$mod: ident,
		$module: ident,
		$runtime: ident,
		with Storage
		$(with $kws:ident)*
	) => {
		{
			$mod::$module::<$runtime>::store_metadata_register(&mut $registry);
			Some($crate::metadata::DecodeDifferent::Encode(
				$crate::metadata::FnEncode(
					$mod::$module::<$runtime>::store_metadata_functions
				)
			))
		}
	};
	(
		$registry: ident,
		$mod: ident,
		$module: ident,
		$runtime: ident,
		with $_:ident
		$(with $kws:ident)*
	) => {
		$crate::__runtime_modules_to_metadata_calls_storage!( $registry, $mod, $module, $runtime, $(with $kws)* );
	};
	(
		$registry: ident,
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
		EventMetadata,
		StorageFunctionModifier, StorageFunctionType, FunctionMetadata,
		StorageFunctionMetadata,
		ModuleMetadata, RuntimeMetadataPrefixed
	};
	use crate::codec::{Encode, Decode};
	use parity_codec_derive::{Decode, Encode};
	use substrate_metadata::*;
	use substrate_metadata_derive::EncodeMetadata;

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

	#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, EncodeMetadata)]
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
		type Balance = u64;
		type BlockNumber = u32;
	}

	impl event_module2::Trait for TestRuntime {
		type Origin = Origin;
		type Balance = u64;
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

	#[test]
	fn runtime_metadata() {
		let expected = RuntimeMetadata::V2(
			RuntimeMetadataV2 {
				modules: vec![
					ModuleMetadata {
						name: DecodeDifferent::Encode("system"),
						prefix: DecodeDifferent::Encode(FnEncode(||"")),
						storage: None,
						calls: None,
						event: Some(DecodeDifferent::Encode(
							FnEncode(|| vec![
								EventMetadata {
									name: DecodeDifferent::Encode("SystemEvent"),
									arguments: Vec::new(),
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
							DecodeDifferent::Encode(FnEncode(|| vec![
								FunctionMetadata {
									name: DecodeDifferent::Encode("aux_0"),
									arguments: Vec::new(),
									documentation: DecodeDifferent::Encode(&[]),
								}
							]))),
						event: Some(DecodeDifferent::Encode(
							FnEncode(|| vec![
								EventMetadata {
									name: DecodeDifferent::Encode("TestEvent"),
									arguments: vec![MetadataName::U64],
									documentation: DecodeDifferent::Encode(&[" Hi, I am a comment."])
								}
							])
						)),
					},
					ModuleMetadata {
						name: DecodeDifferent::Encode("event_module2"),
						prefix: DecodeDifferent::Encode(FnEncode(||"TestStorage")),
						storage: Some(DecodeDifferent::Encode(
							FnEncode(|| vec![
								StorageFunctionMetadata {
									name: DecodeDifferent::Encode("StorageMethod"),
									modifier: StorageFunctionModifier::Optional,
									ty: StorageFunctionType::Plain(MetadataName::U32),
									default: DecodeDifferent::Encode(
										DefaultByteGetter(
											&event_module2::__GetByteStructStorageMethod(::std::marker::PhantomData::<TestRuntime>)
										)
									),
									documentation: DecodeDifferent::Encode(&[]),
								}
							])
						)),
						calls: Some(DecodeDifferent::Encode(FnEncode(|| Vec::new()))),
						event: Some(DecodeDifferent::Encode(
							FnEncode(|| vec![
								EventMetadata {
									name: DecodeDifferent::Encode("TestEvent"),
									arguments: vec![MetadataName::U64],
									documentation: DecodeDifferent::Encode(&[])
								}
							])
						)),
					},
				],
				type_registry: MetadataRegistry::new()
			}
		);

		let metadata_encoded = TestRuntime::metadata().encode();
		let metadata_decoded = RuntimeMetadataPrefixed::decode(&mut &metadata_encoded[..]);
		let expected_metadata: RuntimeMetadataPrefixed = expected.into();

		assert_eq!(expected_metadata, metadata_decoded.unwrap());
	}
}
