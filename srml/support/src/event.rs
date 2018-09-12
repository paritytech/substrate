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

/// Implement the `Event` for a module.
///
/// # Simple Event Example:
///
/// ```rust
/// #[macro_use]
/// extern crate srml_support;
/// extern crate parity_codec as codec;
/// #[macro_use]
/// extern crate parity_codec_derive;
/// #[macro_use]
/// extern crate serde_derive;
///
/// decl_event!(
///	   pub enum Event {
///       Success,
///       Failure(String),
///    }
/// );
///# fn main() {}
/// ```
///
/// # Generic Event Example:
///
/// ```rust
/// #[macro_use]
/// extern crate srml_support;
/// extern crate parity_codec as codec;
/// #[macro_use]
/// extern crate parity_codec_derive;
/// #[macro_use]
/// extern crate serde_derive;
///
/// trait Trait {
///     type Balance;
///     type Token;
/// }
///
/// mod event1 {
///     // Event that specifies the generic parameter explicitly (`Balance`).
///     decl_event!(
///	       pub enum Event<T> where Balance = <T as super::Trait>::Balance {
///           Message(Balance),
///        }
///     );
/// }
///
/// mod event2 {
///     // Event that uses the generic parameter `Balance`.
///     // If no name for the generic parameter is speciefied explicitly,
///     // the name will be taken from the type name of the trait.
///     decl_event!(
///	       pub enum Event<T> where <T as super::Trait>::Balance {
///           Message(Balance),
///        }
///     );
/// }
///
/// mod event3 {
///     // And we even support declaring multiple generic parameters!
///     decl_event!(
///	       pub enum Event<T> where <T as super::Trait>::Balance, <T as super::Trait>::Token {
///           Message(Balance, Token),
///        }
///     );
/// }
///# fn main() {}
/// ```
///
/// The syntax for generic events requires the `where`.
#[macro_export]
macro_rules! decl_event {
	(
		$(#[$attr:meta])*
		pub enum Event<$evt_generic_param:ident> where
			$( $( $generic_rename:ident = )* <$generic:ident as $trait:path>::$trait_type:ident ),*
		{
			$(
				$events:tt
			)*
		}
	) => {
		__decl_generic_event!(
			$( #[ $attr ] )*;
			$evt_generic_param;
			$( $( $generic_rename = )* <$generic as $trait>::$trait_type ),*;
			Events { $( $events )* };
		);
	};
	(
		$(#[$attr:meta])*
		pub enum Event {
			$(
				$events:tt
			)*
		}
	) => {
		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, PartialEq, Eq, Encode, Decode)]
		#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
		$(#[$attr])*
		pub enum Event {
			$(
				$events
			)*
		}
		impl From<Event> for () {
			fn from(_: Event) -> () { () }
		}
		impl Event {
			#[allow(dead_code)]
			pub fn event_json_metadata() -> &'static str {
				concat!("{", __events_to_json!(""; $( $events )* ), " }")
			}
		}
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __decl_generic_event {
	(
		$(#[$attr:meta])*;
		$event_generic_param:ident;
		$generic_rename:ident = <$generic:ident as $trait:path>::$trait_type:ident
			$(, $( $rest_gen_rename:ident = )* <$rest_gen:ident as $rest_trait:path>::$rest_trait_type:ident )*;
		Events { $( $events:tt )* };
	) => {
		__decl_generic_event!(
			$( #[ $attr ] )*;
			$event_generic_param;
			$( $( $rest_gen_rename = )* <$rest_gen as $rest_trait>::$rest_trait_type ),*;
			Events { $( $events )* };
			$generic_rename;
			<$generic as $trait>::$trait_type;
		);
	};
	(
		$(#[$attr:meta])*;
		$event_generic_param:ident;
		$generic_rename:ident = <$generic:ident as $trait:path>::$trait_type:ident
			$(, $( $rest_gen_rename:ident = )* <$rest_gen:ident as $rest_trait:path>::$rest_trait_type:ident )*;
		Events { $( $events:tt )* };
		$( $parsed_generic_params:ident ),*;
		$( <$parsed_generic:ident as $parsed_trait:path>::$parsed_trait_type:ident ),*;
	) => {
		__decl_generic_event!(
			$( #[ $attr ] )*;
			$event_generic_param;
			$( $( $rest_gen_rename = )* <$rest_gen as $rest_trait>::$rest_trait_type ),*;
			Events { $( $events )* };
			$( $parsed_generic_params ),*, $generic_rename;
			$( <$parsed_generic as $parsed_trait>::$parsed_trait_type ),*, <$generic as $trait>::$trait_type;
		);
	};
	(
		$(#[$attr:meta])*;
		$event_generic_param:ident;
		<$generic:ident as $trait:path>::$trait_type:ident
			$(, $( $rest_gen_rename:ident = )* <$rest_gen:ident as $rest_trait:path>::$rest_trait_type:ident )*;
		Events { $( $events:tt )* };
	) => {
		__decl_generic_event!(
			$( #[ $attr ] )*;
			$event_generic_param;
			$( $( $rest_gen_rename = )* <$rest_gen as $rest_trait>::$rest_trait_type ),*;
			Events { $( $events )* };
			$trait_type;
			<$generic as $trait>::$trait_type;
		);
	};
	(
		$(#[$attr:meta])*;
		$event_generic_param:ident;
		<$generic:ident as $trait:path>::$trait_type:ident
			$(, $( $rest_gen_rename:ident = )* <$rest_gen:ident as $rest_trait:path>::$rest_trait_type:ident )*;
		Events { $( $events:tt )* };
		$( $parsed_generic_params:ident ),*;
		$( <$parsed_generic:ident as $parsed_trait:path>::$parsed_trait_type:ident ),*;
	) => {
		__decl_generic_event!(
			$( #[ $attr ] )*;
			$event_generic_param;
			$( $( $rest_gen_rename = )* <$rest_gen as $rest_trait>::$rest_trait_type ),*;
			Events { $( $events )* };
			$( $parsed_generic_params ),*, $trait_type;
			$( <$parsed_generic as $parsed_trait>::$parsed_trait_type ),*, <$generic as $trait>::$trait_type;
		);
	};
	(
		$(#[$attr:meta])*;
		$event_generic_param:ident;
		;
		Events { $( $events:tt )* };
		$( $generic_param:ident ),*;
		$( <$generic:ident as $trait:path>::$trait_type:ident ),*;
	) => {
		pub type Event<$event_generic_param> = RawEvent<$( <$generic as $trait>::$trait_type ),*>;
		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, PartialEq, Eq, Encode, Decode)]
		#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
		$(#[$attr])*
		pub enum RawEvent<$( $generic_param ),*> {
			$(
				$events
			)*
		}
		impl<$( $generic_param ),*> From<RawEvent<$( $generic_param ),*>> for () {
			fn from(_: RawEvent<$( $generic_param ),*>) -> () { () }
		}
		impl<$( $generic_param ),*> RawEvent<$( $generic_param ),*> {
			#[allow(dead_code)]
			pub fn event_json_metadata() -> &'static str {
				concat!("{", __events_to_json!(""; $( $events )* ), " }")
			}
		}
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __events_to_json {
	(
		$prefix_str:expr;
		$( #[doc = $doc_attr:tt] )*
		$event:ident( $first_param:path $(, $param:path )* ),
		$( $rest:tt )*
	) => {
		concat!($prefix_str, " ", "\"", stringify!($event), r#"": { "params": [ ""#,
				stringify!($first_param), "\""
				$(, concat!(", \"", stringify!($param), "\"") )*, r#" ], "description": ["#,
				__function_doc_to_json!(""; $( $doc_attr )*), " ] }",
				__events_to_json!(","; $( $rest )*)
		)
	};
	(
		$prefix_str:expr;
		$( #[doc = $doc_attr:tt] )*
		$event:ident,
		$( $rest:tt )*
	) => {
		concat!($prefix_str, " ", "\"", stringify!($event),
				r#"": { "params": null, "description": ["#,
				__function_doc_to_json!(""; $( $doc_attr )*), " ] }",
				__events_to_json!(","; $( $rest )*)
		)
	};
	(
		$prefix_str:expr;
	) => {
		""
	}
}

#[macro_export]
macro_rules! impl_outer_event {
	($(#[$attr:meta])* pub enum $name:ident for $runtime:ident { $( $module:ident ),* }) => {
		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, PartialEq, Eq, Encode, Decode)]
		#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
		$(#[$attr])*
		#[allow(non_camel_case_types)]
		pub enum $name {
			system(system::Event),
			$(
				$module($module::Event<$runtime>),
			)*
		}
		impl From<system::Event> for $name {
			fn from(x: system::Event) -> Self {
				$name::system(x)
			}
		}
		$(
			impl From<$module::Event<$runtime>> for $name {
				fn from(x: $module::Event<$runtime>) -> Self {
					$name::$module(x)
				}
			}
		)*
		__impl_outer_event_json_metadata!($runtime; $name; $( $module )*);
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __impl_outer_event_json_metadata {
	(
		$runtime:ident;
		$event_name:ident;
		$( $module:ident )*
	) => {
		impl $runtime {
			#[allow(dead_code)]
			pub fn outer_event_json_metadata() -> (&'static str, &'static [(&'static str, fn() -> &'static str)]) {
				static METADATA: &[(&str, fn() -> &'static str)] = &[
					("system", system::Event::event_json_metadata)
					$(
						, (
							stringify!($module),
							$module::Event::<$runtime>::event_json_metadata
						)
					)*
				];
				(
					stringify!($event_name),
					METADATA
				)
			}
		}
	}
}

#[cfg(test)]
#[allow(dead_code)]
mod tests {
	use serde;
	use serde_json;

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
		pub trait Trait {
			type Origin;
			type Balance;
		}

		decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
		}

		decl_event!(
			/// Event without renaming the generic parameter `Balance` and `Origin`.
			pub enum Event<T> where <T as Trait>::Balance, <T as Trait>::Origin
			{
				/// Hi, I am a comment.
				TestEvent(Balance, Origin),
				/// Dog
				EventWithoutParams,
			}
		);
	}

	mod event_module2 {
		pub trait Trait {
			type Origin;
			type Balance;
		}

		decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
		}

		decl_event!(
			/// Event with renamed generic parameter
			pub enum Event<T> where
				BalanceRenamed = <T as Trait>::Balance,
				OriginRenamed = <T as Trait>::Origin
			{
				TestEvent(BalanceRenamed),
				TestOrigin(OriginRenamed),
			}
		);
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

	const EXPECTED_METADATA: (&str, &[(&str, &str)]) = (
		"TestEvent", &[
			("system", r#"{ "SystemEvent": { "params": null, "description": [ ] } }"#),
			("event_module",
				concat!(
					"{",
					r#" "TestEvent": { "params": [ "Balance", "Origin" ], "description": [ " Hi, I am a comment." ] },"#,
					r#" "EventWithoutParams": { "params": null, "description": [ " Dog" ] }"#,
					" }"
				)
			),
			("event_module2",
				concat!(
					"{",
					r#" "TestEvent": { "params": [ "BalanceRenamed" ], "description": [ ] },"#,
					r#" "TestOrigin": { "params": [ "OriginRenamed" ], "description": [ ] }"#,
					" }"
				)
			),
		]
	);

	#[test]
	fn outer_event_json_metadata() {
		let metadata = TestRuntime::outer_event_json_metadata();
		assert_eq!(EXPECTED_METADATA.0, metadata.0);
		assert_eq!(EXPECTED_METADATA.1.len(), metadata.1.len());

		for (expected, got) in EXPECTED_METADATA.1.iter().zip(metadata.1.iter()) {
			assert_eq!(expected.0, got.0);
			assert_eq!(expected.1, got.1());
			let _: serde::de::IgnoredAny =
				serde_json::from_str(got.1()).expect(&format!("Is valid json syntax: {}", got.1()));
		}
	}
}
