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
		$( $mod:ident::$module:ident $(with Storage)* ),*
	) => {
		impl $runtime {
			pub fn json_metadata() -> String {
				format!(r#"{{ "events": {events}, "modules": {modules} }}"#,
					events = Self::outer_event_json_metadata(),
					modules = __runtime_impl_json_metadata!($runtime; $( $mod::$module; )*)
				)
			}
		}
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __runtime_impl_json_metadata {
	(
		$runtime: ident;
		$mod:ident::$module:ident;
		$( $rest:tt )*
	) => {
		__runtime_impl_json_metadata!(
			$runtime;
			r#"{{ "prefix": "{}", "module": {} }}"#;
			stringify!($mod), $mod::$module::<$runtime>::json_metadata();
			$( $rest )*)
	};
	(
		$runtime: ident;
		$format_str:expr;
		$( $format_params:expr ),*;
		$mod:ident::$module:ident;
		$( $rest:tt )*
	) => {
		__runtime_impl_json_metadata!(
			$runtime;
			concat!($format_str, r#", {{ "prefix": "{}", "module": {} }}"#);
			$( $format_params, )* stringify!($mod), $mod::$module::<$runtime>::json_metadata();
			$( $rest )*)
	};
	(
		$runtime: ident;
		$mod:ident::$module:ident with Storage;
		$( $rest:tt )*
	) => {
		__runtime_impl_json_metadata!(
			$runtime;
			r#"{{ "prefix": "{}", "module": {}, "storage": {} }}"#;
			stringify!($mod), $mod::$module::<$runtime>::json_metadata(),
			$mod::$module::<$runtime>::store_json_metadata(); $( $rest )*)
	};
	(
		$runtime: ident;
		$format_str:expr;
		$( $format_params:expr ),*;
		$mod:ident::$module:ident with Storage;
		$( $rest:tt )*
	) => {
		__runtime_impl_json_metadata!(
			$runtime;
			concat!($format_str, r#", {{ "prefix": "{}", "module": {}, "storage": {} }}"#);
			$( $format_params, )* stringify!($mod), $mod::$module::<$runtime>::json_metadata(),
			$mod::$module::<$runtime>::store_json_metadata(); $( $rest )*)
	};
	(
		$runtime:ident;
		$format_str:expr;
		$( $format_params:expr ),*;
	) => {
		format!(concat!("[ ", $format_str, " ]"), $( $format_params, )*)
	};
	// No modules
	() => { "null" }
}

#[cfg(test)]
// Do not complain about unused `dispatch` and `dispatch_aux`.
#[allow(dead_code)]
mod tests {
	use serde;
	use serde_json;
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
			pub struct Module<T: Trait>;

			#[derive(Serialize, Deserialize)]
			pub enum Call where aux: T::PublicAux {
				fn aux_0(aux) -> Result;
			}
		}

		impl<T: Trait> Module<T> {
			fn aux_0(_: &T::PublicAux) -> Result {
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
			pub struct ModuleWithStorage<T: Trait>;
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
		 type PublicAux;
	}

	impl Trait for TestRuntime {
		type PublicAux = u32;
	}

	impl_json_metadata!(
		for TestRuntime with modules
			event_module::Module,
			event_module2::ModuleWithStorage with Storage
	);

	const EXPECTED_METADATA: &str = concat!(
		r#"{ "events": { "name": "TestEvent", "items": "#,
			r#"{ "system": "system::Event", "event_module": "event_module::Event<TestRuntime>", "#,
				r#""event_module2": "event_module2::Event<TestRuntime>" } }, "#,
		r#""modules": [ "#,
			r#"{ "prefix": "event_module", "#,
				r#""module": { "name": "Module", "calls": [ "#,
					r#"{ "name": "Call", "functions": "#,
						r#"{ "0": { "name": "aux_0", "params": [ "#,
							r#"{ "name": "aux", "type": "T::PublicAux" } ], "#,
							r#""description": [ ] } } } ] } }, "#,
			r#"{ "prefix": "event_module2", "module": "#,
				r#"{ "name": "ModuleWithStorage", "calls": [ ] } } ] }"#);

	#[test]
	fn runtime_json_metadata() {
		let metadata = TestRuntime::json_metadata();
		assert_eq!(EXPECTED_METADATA, metadata);
		let _: serde::de::IgnoredAny =
			serde_json::from_str(&metadata).expect("Is valid json syntax");
	}
}
