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

use alloc;
pub use substrate_metadata::JsonMetadata;

/// Make Box available on `std` and `no_std`.
pub type Box<T> = alloc::boxed::Box<T>;
/// Make Vec available on `std` and `no_std`.
pub type Vec<T> = alloc::vec::Vec<T>;

/// Implements the json metadata support for the given runtime and all its modules.
///
/// Example:
/// ```compile_fail
/// impl_json_metadata!(for RUNTIME_NAME with modules MODULE0, MODULE2, MODULE3 with Storage);
/// ```
///
/// In this example, just `MODULE3` implements the `Storage` trait.
#[macro_export]
macro_rules! impl_json_metadata {
	(
		for $runtime:ident with modules
		$( $rest:tt )*
	) => {
		impl $runtime {
			pub fn json_metadata() -> $crate::metadata::Vec<$crate::metadata::JsonMetadata> {
				let events = Self::outer_event_json_metadata();
				__impl_json_metadata!($runtime;
					$crate::metadata::JsonMetadata::Events {
						name: events.0,
						events: events.1,
					};
					$( $rest )*
				)
			}
		}
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __impl_json_metadata {
	(
		$runtime: ident;
		$( $metadata:expr ),*;
		$mod:ident::$module:ident,
		$( $rest:tt )*
	) => {
		__impl_json_metadata!(
			$runtime;
			$( $metadata, )* $crate::metadata::JsonMetadata::Module {
				module: $mod::$module::<$runtime>::json_metadata(), prefix: stringify!($mod)
			};
			$( $rest )*
		)
	};
	(
		$runtime: ident;
		$( $metadata:expr ),*;
		$mod:ident::$module:ident
	) => {
		__impl_json_metadata!(
			$runtime;
			$( $metadata, )* $crate::metadata::JsonMetadata::Module {
				module: $mod::$module::<$runtime>::json_metadata(), prefix: stringify!($mod)
			};
		)
	};
	(
		$runtime: ident;
		$( $metadata:expr ),*;
		$mod:ident::$module:ident with Storage,
		$( $rest:tt )*
	) => {
		__impl_json_metadata!(
			$runtime;
			$( $metadata, )* $crate::metadata::JsonMetadata::ModuleWithStorage {
				module: $mod::$module::<$runtime>::json_metadata(), prefix: stringify!($mod),
				storage: $mod::$module::<$runtime>::store_json_metadata()
			};
			$( $rest )*
		)
	};
	(
		$runtime: ident;
		$( $metadata:expr ),*;
		$mod:ident::$module:ident with Storage
	) => {
		__impl_json_metadata!(
			$runtime;
			$( $metadata, )* $crate::metadata::JsonMetadata::ModuleWithStorage {
				module: $mod::$module::<$runtime>::json_metadata(), prefix: stringify!($mod),
				storage: $mod::$module::<$runtime>::store_json_metadata()
			};
		)
	};
	(
		$runtime:ident;
		$( $metadata:expr ),*;
	) => {
		<[_]>::into_vec($crate::metadata::Box::new([ $( $metadata ),* ]))
	};
}

#[cfg(test)]
// Do not complain about unused `dispatch` and `dispatch_aux`.
#[allow(dead_code)]
mod tests {
	use super::*;
	use serde;
	use serde_json;
	use substrate_metadata::JsonMetadataDecodable;
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
			event_module, event_module2
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

	fn system_event_json() -> &'static str {
		r#"{ "SystemEvent": { "params": null, "description": [ ] } }"#
	}

	fn event_module_event_json() -> &'static str {
		r#"{ "TestEvent": { "params": [ "Balance" ], "description": [ " Hi, I am a comment." ] } }"#
	}

	fn event_module2_event_json() -> &'static str {
		r#"{ "TestEvent": { "params": [ "Balance" ], "description": [ ] } }"#
	}

	impl_json_metadata!(
		for TestRuntime with modules
			event_module::Module,
			event_module2::ModuleWithStorage with Storage
	);

	const EXPECTED_METADATA: &[JsonMetadata] = &[
		JsonMetadata::Events {
			name: "TestEvent",
			events: &[
				("system", system_event_json),
				("event_module", event_module_event_json),
				("event_module2", event_module2_event_json),
			]
		},
		JsonMetadata::Module {
			module: concat!(
				r#"{ "name": "Module", "call": "#,
					r#"{ "name": "Call", "functions": "#,
						r#"{ "0": { "name": "aux_0", "params": [ "#,
							r#"{ "name": "origin", "type": "T::Origin" } ], "#,
							r#""description": [ ] } } } }"#
			),
			prefix: "event_module"
		},
		JsonMetadata::ModuleWithStorage {
			module: r#"{ "name": "ModuleWithStorage", "call": { "name": "Call", "functions": { } } }"#,
			prefix: "event_module2",
			storage: concat!(
				r#"{ "prefix": "TestStorage", "items": { "#,
					r#""StorageMethod": { "description": [ ], "modifier": null, "type": "u32" }"#,
				r#" } }"#
			)
		}
	];

	#[test]
	fn runtime_json_metadata() {
		let metadata = TestRuntime::json_metadata();
		assert_eq!(EXPECTED_METADATA, &metadata[..]);
	}

	#[test]
	fn json_metadata_encode_and_decode() {
		let metadata = TestRuntime::json_metadata();
		let metadata_encoded = metadata.encode();
		let metadata_decoded = Vec::<JsonMetadataDecodable>::decode(&mut &metadata_encoded[..]);

		assert_eq!(&metadata_decoded.unwrap()[..], &metadata[..]);
	}

	#[test]
	fn into_json_string_is_valid_json() {
		let metadata = TestRuntime::json_metadata();
		let metadata_encoded = metadata.encode();
		let metadata_decoded = Vec::<JsonMetadataDecodable>::decode(&mut &metadata_encoded[..]);

		for mdata in metadata_decoded.unwrap().into_iter() {
			let json = mdata.into_json_string();
			let _: serde::de::IgnoredAny =
				serde_json::from_str(&json.1).expect(&format!("Is valid json syntax: {}", json.1));
		}
	}
}
