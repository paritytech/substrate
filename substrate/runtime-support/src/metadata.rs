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
			pub fn json_metadata() -> Vec<$crate::metadata::JSONMetadata> {
					__impl_json_metadata!($runtime;
						$crate::metadata::JSONMetadata::Events {
							events: Self::outer_event_json_metadata()
						};
						$( $rest )*
					)
			}
		}
	}
}

#[derive(Eq, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
#[allow(dead_code)]
pub enum JSONMetadata {
	Events { events: &'static str },
	Module { module: &'static str, prefix: &'static str },
	ModuleWithStorage { module: &'static str, prefix: &'static str, storage: &'static str }
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
			$( $metadata, )* $crate::metadata::JSONMetadata::Module {
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
			$( $metadata, )* $crate::metadata::JSONMetadata::Module {
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
			$( $metadata, )* $crate::metadata::JSONMetadata::ModuleWithStorage {
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
			$( $metadata, )* $crate::metadata::JSONMetadata::ModuleWithStorage {
				module: $mod::$module::<$runtime>::json_metadata(), prefix: stringify!($mod),
				storage: $mod::$module::<$runtime>::store_json_metadata()
			};
		)
	};
	(
		$runtime:ident;
		$( $metadata:expr ),*;
	) => {
		vec![ $( $metadata ),* ]
	};
}

#[cfg(test)]
// Do not complain about unused `dispatch` and `dispatch_aux`.
#[allow(dead_code)]
mod tests {
	use super::*;
	use dispatch::Result;

	mod system {
		#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, Deserialize, Serialize)]
		pub struct Event;
	}

	mod event_module {
		use super::*;

		#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, Deserialize, Serialize)]
		pub struct Event<T> {
			t: T,
		}

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
		use super::*;

		#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, Deserialize, Serialize)]
		pub struct Event<T> {
			t: T,
		}

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

	pub trait Trait {
		 type Origin;
	}

	impl Trait for TestRuntime {
		type Origin = u32;
	}

	impl_json_metadata!(
		for TestRuntime with modules
			event_module::Module,
			event_module2::ModuleWithStorage with Storage
	);

	const EXPECTED_METADATA: &[JSONMetadata] = &[
		JSONMetadata::Events {
			events: concat!(
				r#"{ "name": "TestEvent", "items": "#,
					r#"{ "system": "system::Event", "#,
					r#""event_module": "event_module::Event<TestRuntime>", "#,
					r#""event_module2": "event_module2::Event<TestRuntime>" } }"#)
		},
		JSONMetadata::Module {
			module: concat!(
				r#"{ "name": "Module", "call": "#,
					r#"{ "name": "Call", "functions": "#,
						r#"{ "0": { "name": "aux_0", "params": [ "#,
							r#"{ "name": "origin", "type": "T::Origin" } ], "#,
							r#""description": [ ] } } } }"#
			),
			prefix: "event_module"
		},
		JSONMetadata::ModuleWithStorage {
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
}
