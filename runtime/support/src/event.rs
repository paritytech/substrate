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

/// Implement an `Event`/`RawEvent` for a module.
#[macro_export]
macro_rules! decl_event {
	(
		$(#[$attr:meta])*
		pub enum Event<$( $evt_generic_param:ident )*> with RawEvent<$( $generic_param:ident ),*>
			where $( <$generic:ident as $trait:path>::$trait_type:ident),* {
			$(
				$(#[doc = $doc_attr:tt])*
				$event:ident( $( $param:path ),* ),
			)*
		}
	) => {
		pub type Event<$( $evt_generic_param )*> = RawEvent<$( <$generic as $trait>::$trait_type ),*>;
		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, PartialEq, Eq, Encode, Decode)]
		#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
		$(#[$attr])*
		pub enum RawEvent<$( $generic_param ),*> {
			$(
				$( #[doc = $doc_attr] )*
				$event($( $param ),*),
			)*
		}
		impl<$( $generic_param ),*> From<RawEvent<$( $generic_param ),*>> for () {
			fn from(_: RawEvent<$( $generic_param ),*>) -> () { () }
		}
		impl<$( $generic_param ),*> RawEvent<$( $generic_param ),*> {
			#[allow(dead_code)]
			pub fn event_json_metadata() -> &'static str {
				concat!(
					"{",
					__impl_event_json_metadata!("";
						$(
							$event ( $( $param ),* );
							__function_doc_to_json!(""; $($doc_attr)*);
						)*
					),
					" }"
				)
			}
		}
	};
	(
		$(#[$attr:meta])*
		pub enum Event {
			$(
				$(#[doc = $doc_attr:tt])*
				$event:ident,
			)*
		}
	) => {
		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, PartialEq, Eq, Encode, Decode)]
		#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
		$(#[$attr])*
		pub enum Event {
			$(
				$( #[doc = $doc_attr] )*
				$event,
			)*
		}
		impl From<Event> for () {
			fn from(_: Event) -> () { () }
		}
		impl Event {
			#[allow(dead_code)]
			pub fn event_json_metadata() -> &'static str {
				concat!(
					"{",
					__impl_event_json_metadata!("";
						$(
							$event;
							__function_doc_to_json!(""; $($doc_attr)*);
						)*
					),
					" }"
				)
			}
		}
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __impl_event_json_metadata {
	(
		$prefix_str:expr;
		$event:ident( $first_param:path $(, $param:path )* );
		$event_doc:expr;
		$( $rest:tt )*
	) => {
		concat!($prefix_str, " ", "\"", stringify!($event), r#"": { "params": [ ""#,
				stringify!($first_param), "\""
				$(, concat!(", \"", stringify!($param), "\"") )*, r#" ], "description": ["#,
				$event_doc, " ] }",
				__impl_event_json_metadata!(","; $( $rest )*)
		)
	};
	(
		$prefix_str:expr;
		$event:ident;
		$event_doc:expr;
		$( $rest:tt )*
	) => {
		concat!($prefix_str, " ", "\"", stringify!($event),
				r#"": { "params": null, "description": ["#, $event_doc, " ] }",
				__impl_event_json_metadata!(","; $( $rest )*)
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
			pub enum Event<T> with RawEvent<Balance>
				where <T as Trait>::Balance
			{
				/// Hi, I am a comment.
				TestEvent(Balance),
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
			pub enum Event<T> with RawEvent<Balance>
				where <T as Trait>::Balance
			{
				TestEvent(Balance),
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
			("event_module", r#"{ "TestEvent": { "params": [ "Balance" ], "description": [ " Hi, I am a comment." ] } }"#),
			("event_module2", r#"{ "TestEvent": { "params": [ "Balance" ], "description": [ ] } }"#),
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
