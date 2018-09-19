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

pub use substrate_metadata::{
	DecodeDifferent, FnEncode, RuntimeMetadata, RuntimeModuleMetadata
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
			pub fn metadata() -> $crate::metadata::RuntimeMetadata {
				$crate::metadata::RuntimeMetadata {
					outer_event: Self::outer_event_metadata(),
					modules: __runtime_modules_to_metadata!($runtime;; $( $rest )*),
				}
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
		$mod:ident::$module:ident,
		$( $rest:tt )*
	) => {
		__runtime_modules_to_metadata!(
			$runtime;
			$( $metadata, )* $crate::metadata::RuntimeModuleMetadata {
				prefix: $crate::metadata::DecodeDifferent::Encode(stringify!($mod)),
				module: $crate::metadata::DecodeDifferent::Encode(
					$crate::metadata::FnEncode($mod::$module::<$runtime>::metadata)
				),
				storage: None,
			};
			$( $rest )*
		)
	};
	(
		$runtime: ident;
		$( $metadata:expr ),*;
		$mod:ident::$module:ident with Storage,
		$( $rest:tt )*
	) => {
		__runtime_modules_to_metadata!(
			$runtime;
			$( $metadata, )* $crate::metadata::RuntimeModuleMetadata {
				prefix: $crate::metadata::DecodeDifferent::Encode(stringify!($mod)),
				module: $crate::metadata::DecodeDifferent::Encode(
					$crate::metadata::FnEncode($mod::$module::<$runtime>::metadata)
				),
				storage: Some($crate::metadata::DecodeDifferent::Encode(
					$crate::metadata::FnEncode($mod::$module::<$runtime>::store_metadata)
				)),
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

#[cfg(test)]
// Do not complain about unused `dispatch` and `dispatch_aux`.
#[allow(dead_code)]
mod tests {
	use super::*;
	use substrate_metadata::{
		EventMetadata, OuterEventMetadata, RuntimeModuleMetadata, CallMetadata, ModuleMetadata,
		StorageFunctionModifier, StorageFunctionType, FunctionMetadata, FunctionArgumentMetadata,
		StorageMetadata, StorageFunctionMetadata,
	};
	use codec::{Decode, Encode};

	mod system {
		pub trait Trait {
			type Origin;
		}

		decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
		}

		decl_event!(
			pub enum Event {
				SystemEvent,
			}
		);
	}

	mod event_module {
		use dispatch::Result;

		pub trait Trait {
			type Origin;
			type Balance;
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
				fn aux_0(origin) -> Result;
			}
		}

		impl<T: Trait> Module<T> {
			fn aux_0(_: T::Origin) -> Result {
				unreachable!()
			}
		}
	}

	mod event_module2 {
		pub trait Trait {
			type Origin;
			type Balance;
		}

		decl_event!(
			pub enum Event<T> where <T as Trait>::Balance
			{
				TestEvent(Balance),
			}
		);

		decl_module! {
			pub struct ModuleWithStorage<T: Trait> for enum Call where origin: T::Origin {}
		}

		decl_storage! {
			trait Store for ModuleWithStorage<T: Trait> as TestStorage {
				StorageMethod : u32;
			}
		}
	}

	#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, Deserialize, Serialize)]
	pub struct TestRuntime;

	impl_outer_event! {
		pub enum TestEvent for TestRuntime {
			event_module<T>,
			event_module2<T>,
		}
	}

	impl event_module::Trait for TestRuntime {
		type Origin = u32;
		type Balance = u32;
	}

	impl event_module2::Trait for TestRuntime {
		type Origin = u32;
		type Balance = u32;
	}

	impl system::Trait for TestRuntime {
		type Origin = u32;
	}

	impl_runtime_metadata!(
		for TestRuntime with modules
			event_module::Module,
			event_module2::ModuleWithStorage with Storage,
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
								 arguments: DecodeDifferent::Encode(&[
									 FunctionArgumentMetadata {
										 name: DecodeDifferent::Encode("origin"),
										 ty: DecodeDifferent::Encode("T::Origin"),
									 }
								 ]),
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
					 name: DecodeDifferent::Encode("ModuleWithStorage"),
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
							   modifier: StorageFunctionModifier::None,
							   ty: StorageFunctionType::Plain(DecodeDifferent::Encode("u32")),
							   documentation: DecodeDifferent::Encode(&[]),
						   }
					   ])
					}
				))),
			}
		])
	};

	#[test]
	fn runtime_metadata() {
		let metadata = TestRuntime::metadata();
		assert_eq!(EXPECTED_METADATA, metadata);

		let metadata_encoded = metadata.encode();
		let metadata_decoded = RuntimeMetadata::decode(&mut &metadata_encoded[..]);

		assert_eq!(metadata, metadata_decoded.unwrap());
	}
}
