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

use codec::{Encode, Output};
#[cfg(feature = "std")]
use codec::{Decode, Input};
use alloc;

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
			pub fn json_metadata() -> $crate::metadata::Vec<$crate::metadata::JSONMetadata> {
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

/// The metadata of a runtime encoded as JSON.
#[derive(Eq, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum JSONMetadata {
	Events { events: &'static str },
	Module { module: &'static str, prefix: &'static str },
	ModuleWithStorage { module: &'static str, prefix: &'static str, storage: &'static str }
}

impl Encode for JSONMetadata {
	fn encode_to<W: Output>(&self, dest: &mut W) {
		match self {
			JSONMetadata::Events { events } => {
				0i8.encode_to(dest);
				events.encode_to(dest);
			},
			JSONMetadata::Module { module, prefix } => {
				1i8.encode_to(dest);
				prefix.encode_to(dest);
				module.encode_to(dest);
			},
			JSONMetadata::ModuleWithStorage { module, prefix, storage } => {
				2i8.encode_to(dest);
				prefix.encode_to(dest);
				module.encode_to(dest);
				storage.encode_to(dest);
			}
		}
	}
}

/// Utility struct for making `JSONMetadata` decodeable.
#[derive(Eq, PartialEq, Debug)]
#[cfg(feature = "std")]
pub enum JSONMetadataDecodable {
	Events { events: String },
	Module { module: String, prefix: String },
	ModuleWithStorage { module: String, prefix: String, storage: String }
}

#[cfg(feature = "std")]
impl JSONMetadataDecodable {
	/// Returns the instance as JSON string.
	/// The first value of the tuple is the name of the metadata type and the second in the JSON string.
	pub fn into_json_string(self) -> (&'static str, String) {
		match self {
			JSONMetadataDecodable::Events { events } => {
				("events", events)
			},
			JSONMetadataDecodable::Module { prefix, module } => {
				("module", format!(r#"{{ "prefix": "{}", "module": {} }}"#, prefix, module))
			},
			JSONMetadataDecodable::ModuleWithStorage { prefix, module, storage } => {
				("moduleWithStorage",
				 format!(r#"{{ "prefix": "{}", "module": {}, "storage": {} }}"#, prefix, module, storage))
			}
		}
	}
}

#[cfg(feature = "std")]
impl Decode for JSONMetadataDecodable {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		i8::decode(input).and_then(|variant| {
			match variant {
				0 => String::decode(input)
						.and_then(|events| Some(JSONMetadataDecodable::Events { events })),
				1 => String::decode(input)
						.and_then(|prefix| String::decode(input).map(|v| (prefix, v)))
						.and_then(|(prefix, module)| Some(JSONMetadataDecodable::Module { prefix, module })),
				2 => String::decode(input)
						.and_then(|prefix| String::decode(input).map(|v| (prefix, v)))
						.and_then(|(prefix, module)| String::decode(input).map(|v| (prefix, module, v)))
						.and_then(|(prefix, module, storage)| Some(JSONMetadataDecodable::ModuleWithStorage { prefix, module, storage })),
				_ => None,
			}
		})
	}
}

#[cfg(test)]
impl PartialEq<JSONMetadata> for JSONMetadataDecodable {
	fn eq(&self, other: &JSONMetadata) -> bool {
		match (self, other) {
			(
				JSONMetadataDecodable::Events { events: left },
				JSONMetadata::Events { events: right }
			) => {
				left == right
			},
			(
				JSONMetadataDecodable::Module { prefix: lpre, module: lmod },
				JSONMetadata::Module { prefix: rpre, module: rmod }
			) => {
				lpre == rpre && lmod == rmod
			},
			(
				JSONMetadataDecodable::ModuleWithStorage { prefix: lpre, module: lmod, storage: lstore },
				JSONMetadata::ModuleWithStorage { prefix: rpre, module: rmod, storage: rstore }
			) => {
				lpre == rpre && lmod == rmod && lstore == rstore
			},
			_ => false,
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
		<[_]>::into_vec($crate::metadata::Box::new([ $( $metadata ),* ]))
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

	#[test]
	fn json_metadata_encode_and_decode() {
		let metadata = TestRuntime::json_metadata();
		let metadata_encoded = metadata.encode();
		let metadata_decoded = Vec::<JSONMetadataDecodable>::decode(&mut &metadata_encoded[..]);

		assert_eq!(&metadata_decoded.unwrap()[..], &metadata[..]);
	}
}
