// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

pub use frame_metadata::{
    v14::{
        PalletErrorMetadata, PalletEventMetadata, ExtrinsicMetadata, FunctionArgumentMetadata,
        FunctionMetadata, PalletCallMetadata, PalletMetadata, PalletConstantMetadata, PalletStorageMetadata,
        RuntimeMetadataLastVersion, SignedExtensionMetadata,
        StorageEntryMetadata, StorageEntryModifier, StorageEntryType, StorageHasher, TypeSpec,
    },
	RuntimeMetadata, RuntimeMetadataPrefixed,
};

/// todo: [AJ] update docs
/// Implements the metadata support for the given runtime and all its modules.
///
/// Example:
/// ```
///# mod module0 {
///#    pub trait Config: 'static {
///#        type Origin;
///#        type BlockNumber;
///#        type PalletInfo: frame_support::traits::PalletInfo;
///#        type DbWeight: frame_support::traits::Get<frame_support::weights::RuntimeDbWeight>;
///#    }
///#    frame_support::decl_module! {
///#        pub struct Module<T: Config> for enum Call where origin: T::Origin, system=self {}
///#    }
///#
///#    frame_support::decl_storage! {
///#        trait Store for Module<T: Config> as TestStorage {}
///#    }
///# }
///# use module0 as module1;
///# use module0 as module2;
///# impl frame_support::traits::PalletInfo for Runtime {
///#     fn index<P: 'static>() -> Option<usize> { unimplemented!() }
///#     fn name<P: 'static>() -> Option<&'static str> { unimplemented!() }
///# }
///# impl module0::Config for Runtime {
///#     type Origin = u32;
///#     type BlockNumber = u32;
///#     type PalletInfo = Self;
///#     type DbWeight = ();
///# }
///#
///# type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<(), (), (), ()>;
///
/// struct Runtime;
/// frame_support::impl_runtime_metadata! {
///     for Runtime with pallets where Extrinsic = UncheckedExtrinsic
///         module0::Module as Module0 { index 0 } with,
///         module1::Module as Module1 { index 1 } with,
///         module2::Module as Module2 { index 2 } with Storage,
/// };
/// ```
///
/// In this example, just `MODULE3` implements the `Storage` trait.
#[macro_export]
macro_rules! impl_runtime_metadata {
	(
		for $runtime:ident with pallets where Extrinsic = $ext:ident
			$( $rest:tt )*
	) => {
		impl $runtime {
			pub fn metadata() -> $crate::metadata::RuntimeMetadataPrefixed {
				$crate::metadata::RuntimeMetadataLastVersion::new(
					$crate::__runtime_modules_to_metadata!($runtime;; $( $rest )*),
					$crate::metadata::ExtrinsicMetadata {
						ty: $crate::scale_info::meta_type::<$ext>(),
						version: <$ext as $crate::sp_runtime::traits::ExtrinsicMetadata>::VERSION,
						signed_extensions: <
								<
									$ext as $crate::sp_runtime::traits::ExtrinsicMetadata
								>::SignedExtensions as $crate::sp_runtime::traits::SignedExtension
							>::identifier()
								.into_iter()
								.map(|(id, ty)| $crate::metadata::SignedExtensionMetadata {
									identifier: id,
									ty,
								})
								.collect(),
					},
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
		$mod:ident::$module:ident $( < $instance:ident > )? as $name:ident
			{ index $index:tt }
			$(with)+ $($kw:ident)*
		,
		$( $rest:tt )*
	) => {
		$crate::__runtime_modules_to_metadata!(
			$runtime;
			$( $metadata, )* $crate::metadata::PalletMetadata {
				name: stringify!($name),
				index: $index,
				storage: $crate::__runtime_modules_to_metadata_calls_storage!(
					$mod, $module $( <$instance> )?, $runtime, $(with $kw)*
				),
				calls: $crate::__runtime_modules_to_metadata_calls_call!(
					$mod, $module $( <$instance> )?, $runtime, $(with $kw)*
				),
				event: $crate::__runtime_modules_to_metadata_calls_event!(
					$mod, $module $( <$instance> )?, $runtime, $(with $kw)*
				),
				constants: $mod::$module::<$runtime $(, $mod::$instance )?>::module_constants_metadata(),
				error: $mod::$module::<$runtime $(, $mod::$instance )?>::error_metadata(),
			};
			$( $rest )*
		)
	};
	(
		$runtime:ident;
		$( $metadata:expr ),*;
	) => {
		vec![ $( $metadata ),* ]
	};
}

#[macro_export]
#[doc(hidden)]
macro_rules! __runtime_modules_to_metadata_calls_call {
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with Call
		$(with $kws:ident)*
	) => {
		Some($mod::$module::<$runtime $(, $mod::$instance )?>::call_functions())
	};
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with $_:ident
		$(with $kws:ident)*
	) => {
		$crate::__runtime_modules_to_metadata_calls_call! {
			$mod, $module $( <$instance> )?, $runtime, $(with $kws)*
		};
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
		Some($crate::paste::expr!{
				$runtime:: [< __module_events_ $mod $(_ $instance)?>]()
			}
		)
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
macro_rules! __runtime_modules_to_metadata_calls_storage {
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with Storage
		$(with $kws:ident)*
	) => {
		Some($mod::$module::<$runtime $(, $mod::$instance )?>::storage_metadata())
	};
	(
		$mod: ident,
		$module: ident $( <$instance:ident> )?,
		$runtime: ident,
		with $_:ident
		$(with $kws:ident)*
	) => {
		$crate::__runtime_modules_to_metadata_calls_storage! {
			$mod, $module $( <$instance> )?, $runtime, $(with $kws)*
		};
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
	use codec::{Encode, Decode};
	use crate::traits::Get;
	use sp_runtime::transaction_validity::TransactionValidityError;

	#[derive(Clone, Eq, Debug, PartialEq, Encode, Decode, scale_info::TypeInfo)]
	struct TestExtension;
	impl sp_runtime::traits::SignedExtension for TestExtension {
		type AccountId = u32;
		type Call = ();
		type AdditionalSigned = u32;
		type Pre = ();
		const IDENTIFIER: &'static str = "testextension";
		fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
			Ok(1)
		}
	}

	#[derive(Clone, Eq, Debug, PartialEq, Encode, Decode, scale_info::TypeInfo)]
	struct TestExtension2;
	impl sp_runtime::traits::SignedExtension for TestExtension2 {
		type AccountId = u32;
		type Call = ();
		type AdditionalSigned = u32;
		type Pre = ();
		const IDENTIFIER: &'static str = "testextension2";
		fn additional_signed(&self) -> Result<Self::AdditionalSigned, TransactionValidityError> {
			Ok(1)
		}
	}

	#[derive(scale_info::TypeInfo)]
	struct TestExtrinsic;

	impl sp_runtime::traits::ExtrinsicMetadata for TestExtrinsic {
		const VERSION: u8 = 1;
		type SignedExtensions = (TestExtension, TestExtension2);
	}

	mod system {
		use super::*;

		pub trait Config: scale_info::TypeInfo + 'static {
			type BaseCallFilter;
			const ASSOCIATED_CONST: u64 = 500;
			type Origin: Into<Result<RawOrigin<Self::AccountId>, Self::Origin>>
				+ From<RawOrigin<Self::AccountId>>;
			type AccountId: From<u32> + Encode + scale_info::TypeInfo;
			type BlockNumber: From<u32> + Encode + scale_info::TypeInfo;
			type SomeValue: Get<u32>;
			type PalletInfo: crate::traits::PalletInfo;
			type DbWeight: crate::traits::Get<crate::weights::RuntimeDbWeight>;
			type Call;
		}

		decl_module! {
			pub struct Module<T: Config> for enum Call where origin: T::Origin, system=self {
				/// Hi, I am a comment.
				const BlockNumber: T::BlockNumber = 100.into();
				const GetType: T::AccountId = T::SomeValue::get().into();
				const ASSOCIATED_CONST: u64 = T::ASSOCIATED_CONST.into();
			}
		}

		decl_event!(
			pub enum Event {
				SystemEvent,
			}
		);

		#[derive(Clone, PartialEq, Eq, Debug, Encode, Decode, scale_info::TypeInfo)]
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

		pub type Origin<T> = RawOrigin<<T as Config>::AccountId>;
	}

	mod event_module {
		use crate::dispatch::DispatchResult;
		use super::system;

		pub trait Config: system::Config {
			type Balance;
		}

		decl_event!(
			pub enum Event<T> where <T as Config>::Balance
			{
				/// Hi, I am a comment.
				TestEvent(Balance),
			}
		);

		decl_module! {
			pub struct Module<T: Config> for enum Call where origin: T::Origin, system=system {
				type Error = Error<T>;

				#[weight = 0]
				fn aux_0(_origin) -> DispatchResult { unreachable!() }
			}
		}

		crate::decl_error! {
			pub enum Error for Module<T: Config> {
				/// Some user input error
				UserInputError,
				/// Something bad happened
				/// this could be due to many reasons
				BadThingHappened,
			}
		}
	}

	mod event_module2 {
		use super::system;

		pub trait Config: system::Config {
			type Balance;
		}

		decl_event!(
			pub enum Event<T> where <T as Config>::Balance
			{
				TestEvent(Balance),
			}
		);

		decl_module! {
			pub struct Module<T: Config> for enum Call where origin: T::Origin, system=system {}
		}

		crate::decl_storage! {
			trait Store for Module<T: Config> as TestStorage {
				StorageMethod : Option<u32>;
			}
			add_extra_genesis {
				build(|_| {});
			}
		}
	}

	type EventModule = event_module::Module<TestRuntime>;
	type EventModule2 = event_module2::Module<TestRuntime>;

	#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, scale_info::TypeInfo)]
	pub struct TestRuntime;

	impl crate::traits::PalletInfo for TestRuntime {
		fn index<P: 'static>() -> Option<usize> {
			let type_id = sp_std::any::TypeId::of::<P>();
			if type_id == sp_std::any::TypeId::of::<system::Pallet<TestRuntime>>() {
				return Some(0)
			}
			if type_id == sp_std::any::TypeId::of::<EventModule>() {
				return Some(1)
			}
			if type_id == sp_std::any::TypeId::of::<EventModule2>() {
				return Some(2)
			}

			None
		}
		fn name<P: 'static>() -> Option<&'static str> {
			let type_id = sp_std::any::TypeId::of::<P>();
			if type_id == sp_std::any::TypeId::of::<system::Pallet<TestRuntime>>() {
				return Some("System")
			}
			if type_id == sp_std::any::TypeId::of::<EventModule>() {
				return Some("EventModule")
			}
			if type_id == sp_std::any::TypeId::of::<EventModule2>() {
				return Some("EventModule2")
			}

			None
		}
	}

	impl_outer_event! {
		pub enum TestEvent for TestRuntime {
			system,
			event_module<T>,
			event_module2<T>,
		}
	}

	impl_outer_origin! {
		pub enum Origin for TestRuntime where system = system {}
	}

	impl_outer_dispatch! {
		pub enum Call for TestRuntime where origin: Origin {
			event_module::EventModule,
			event_module2::EventModule2,
		}
	}

	impl event_module::Config for TestRuntime {
		type Balance = u32;
	}

	impl event_module2::Config for TestRuntime {
		type Balance = u32;
	}

	crate::parameter_types! {
		pub const SystemValue: u32 = 600;
	}

	#[test]
	fn runtime_metadata() {
		let pallets = vec![
			PalletMetadata {
				name: "System",
				index: 0,
				storage: None,
				calls: None,
				event: Some(
					PalletEventMetadata {
						ty: scale_info::meta_type::<system::Event>(),
					},
				),
				constants: vec![
					PalletConstantMetadata {
						name: "BlockNumber",
						ty: scale_info::meta_type::<u32>(),
						value: vec![100, 0, 0, 0],
						documentation: vec![
							" Hi, I am a comment.",
						],
					},
					PalletConstantMetadata {
						name: "GetType",
						ty: scale_info::meta_type::<u32>(),
						value: vec![88, 2, 0, 0],
						documentation: vec![],
					},
					PalletConstantMetadata {
						name: "ASSOCIATED_CONST",
						ty: scale_info::meta_type::<u64>(),
						value: vec![244, 1, 0, 0, 0, 0, 0, 0],
						documentation: vec![],
					},
				],
				error: None,
			},
			PalletMetadata {
				name: "Module",
				index: 1,
				storage: None,
				calls: Some(
					PalletCallMetadata {
						ty: scale_info::meta_type::<event_module::Call<TestRuntime>>(),
						calls: vec![
							FunctionMetadata {
								name: "aux_0",
								arguments: vec![],
								documentation: vec![],
							},
						],
					},
				),
				event: Some(
					PalletEventMetadata {
						ty: scale_info::meta_type::<event_module::Event<TestRuntime>>(),
					},
				),
				constants: vec![],
				error: Some(
					PalletErrorMetadata {
						ty: scale_info::meta_type::<event_module::Error<TestRuntime>>(),
					},
				),
			},
			PalletMetadata {
				name: "Module2",
				storage: Some(
					PalletStorageMetadata {
						prefix: "TestStorage",
						entries: vec![
							StorageEntryMetadata {
								name: "StorageMethod",
								modifier: StorageEntryModifier::Optional,
								ty: StorageEntryType::Plain(
									scale_info::meta_type::<u32>(),
								),
								default: vec![0],
								documentation: vec![],
							},
						],
					},
				),
				calls: Some(
					PalletCallMetadata {
						ty: scale_info::meta_type::<event_module2::Call<TestRuntime>>(),
						calls: vec![],
					},
				),
				event: Some(
					PalletEventMetadata {
						ty: scale_info::meta_type::<event_module2::Event<TestRuntime>>(),
					},
				),
				constants: vec![],
				error: None,
				index: 2,
			},
		];
		let extrinsic = ExtrinsicMetadata {
			ty: scale_info::meta_type::<TestExtrinsic>(),
			version: 1,
			signed_extensions: vec![
				SignedExtensionMetadata { identifier: "testextension", ty: scale_info::meta_type::<TestExtension>() },
				SignedExtensionMetadata { identifier: "testextension2", ty: scale_info::meta_type::<TestExtension2>() },
			]
		};

		let expected_metadata: RuntimeMetadataPrefixed = RuntimeMetadataLastVersion::new(pallets, extrinsic).into();
		let expected_metadata = match expected_metadata.1 {
			RuntimeMetadata::V14(metadata) => {
				metadata
			},
			_ => panic!("metadata has been bumped, test needs to be updated"),
		};

		let actual_metadata = match TestRuntime::metadata().1 {
			RuntimeMetadata::V14(metadata) => {
				metadata
			},
			_ => panic!("metadata has been bumped, test needs to be updated"),
		};

		pretty_assertions::assert_eq!(actual_metadata.pallets, expected_metadata.pallets);
		pretty_assertions::assert_eq!(actual_metadata.extrinsic, expected_metadata.extrinsic);
	}

	impl system::Config for TestRuntime {
		type BaseCallFilter = ();
		type Origin = Origin;
		type AccountId = u32;
		type BlockNumber = u32;
		type SomeValue = SystemValue;
		type PalletInfo = Self;
		type DbWeight = ();
		type Call = Call;
	}

	impl_runtime_metadata!(
		for TestRuntime with pallets where Extrinsic = TestExtrinsic
			system::Pallet as System { index 0 } with Event,
			event_module::Module as Module { index 1 } with Event Call,
			event_module2::Module as Module2 { index 2 } with Event Storage Call,
	);
}
