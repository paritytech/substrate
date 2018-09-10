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
			pub fn outer_event_json_metadata() -> &'static str {
				concat!(r#"{ "name": ""#, stringify!($event_name), r#"", "items": { "#,
					r#""system": "system::Event""#,
					$(concat!(", \"", stringify!($module), r#"": ""#, 
						stringify!($module), "::Event<", stringify!($runtime), r#">""#),)*
					" } }")
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use serde;
	use serde_json;

	mod system {
		#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, Deserialize, Serialize)]
		pub struct Event;
	}

	mod event_module {
		#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, Deserialize, Serialize)]
		pub struct Event<T> {
			t: T,
		}
	}

	mod event_module2 {
		#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, Deserialize, Serialize)]
		pub struct Event<T> {
			t: T,
		}
	}

	#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, Deserialize, Serialize)]
	pub struct TestRuntime;

	impl_outer_event! {
		pub enum TestEvent for TestRuntime {
			event_module, event_module2
		}
	}

	const EXPECTED_METADATA: &str = concat!(
		r#"{ "name": "TestEvent", "items": { "#,
			r#""system": "system::Event", "#,
			r#""event_module": "event_module::Event<TestRuntime>", "#,
			r#""event_module2": "event_module2::Event<TestRuntime>" "#,
		r#"} }"#
	);

	#[test]
	fn outer_event_json_metadata() {
		let metadata = TestRuntime::outer_event_json_metadata();
		assert_eq!(EXPECTED_METADATA, metadata);
		let _: serde::de::IgnoredAny =
			serde_json::from_str(metadata).expect("Is valid json syntax");
	}
}
