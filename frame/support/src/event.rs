// Copyright 2018-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

//! Macros that define an Event types. Events can be used to easily report changes or conditions
//! in your runtime to external entities like users, chain explorers, or dApps.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

pub use frame_metadata::{EventMetadata, DecodeDifferent, OuterEventMetadata, FnEncode};

/// Implement the `Event` for a module.
///
/// # Simple Event Example:
///
/// ```rust
/// frame_support::decl_event!(
///    pub enum Event {
///       Success,
///       Failure(String),
///    }
/// );
///
///# fn main() {}
/// ```
///
/// # Generic Event Example:
///
/// ```rust
/// trait Trait {
///     type Balance;
///     type Token;
/// }
///
/// mod event1 {
///     // Event that specifies the generic parameter explicitly (`Balance`).
///     frame_support::decl_event!(
///        pub enum Event<T> where Balance = <T as super::Trait>::Balance {
///           Message(Balance),
///        }
///     );
/// }
///
/// mod event2 {
///     // Event that uses the generic parameter `Balance`.
///     // If no name for the generic parameter is specified explicitly,
///     // the name will be taken from the type name of the trait.
///     frame_support::decl_event!(
///        pub enum Event<T> where <T as super::Trait>::Balance {
///           Message(Balance),
///        }
///     );
/// }
///
/// mod event3 {
///     // And we even support declaring multiple generic parameters!
///     frame_support::decl_event!(
///        pub enum Event<T> where <T as super::Trait>::Balance, <T as super::Trait>::Token {
///           Message(Balance, Token),
///        }
///     );
/// }
///
///# fn main() {}
/// ```
///
/// The syntax for generic events requires the `where`.
///
/// # Generic Event with Instance Example:
///
/// ```rust
///# struct DefaultInstance;
///# trait Instance {}
///# impl Instance for DefaultInstance {}
/// trait Trait<I: Instance=DefaultInstance> {
///     type Balance;
///     type Token;
/// }
///
/// // For module with instances, DefaultInstance is optional
/// frame_support::decl_event!(
///    pub enum Event<T, I: Instance = DefaultInstance> where
///       <T as Trait>::Balance,
///       <T as Trait>::Token
///    {
///       Message(Balance, Token),
///    }
/// );
///# fn main() {}
/// ```
#[macro_export]
macro_rules! decl_event {
	(
		$(#[$attr:meta])*
		pub enum Event<$evt_generic_param:ident $(, $instance:ident $(: $instantiable:ident)? $( = $event_default_instance:path)? )?> where
			$( $tt:tt )*
	) => {
		$crate::__decl_generic_event!(
			$( #[ $attr ] )*;
			$evt_generic_param;
			$($instance $( = $event_default_instance)? )?;
			{ $( $tt )* };
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
		#[derive(
			Clone, PartialEq, Eq,
			$crate::codec::Encode,
			$crate::codec::Decode,
			$crate::RuntimeDebug,
		)]
		/// Events for this module.
		///
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
			#[doc(hidden)]
			pub fn metadata() -> &'static [ $crate::event::EventMetadata ] {
				$crate::__events_to_metadata!(; $( $events )* )
			}
		}
	}
}

#[macro_export]
#[doc(hidden)]
// This parsing to retrieve last ident on unnamed generic could be improved.
// but user can still name it if the parsing fails. And improving parsing seems difficult.
macro_rules! __decl_generic_event {
	(
		$(#[$attr:meta])*;
		$event_generic_param:ident;
		$($instance:ident $( = $event_default_instance:path)? )?;
		{ $( $tt:tt )* };
	) => {
		$crate::__decl_generic_event!(@format_generic
			$( #[ $attr ] )*;
			$event_generic_param;
			$($instance $( = $event_default_instance)? )?;
			{ $( $tt )* };
			{};
		);
	};
	// Finish formatting on an unnamed one
	(@format_generic
		$(#[$attr:meta])*;
		$event_generic_param:ident;
		$($instance:ident $( = $event_default_instance:path)? )?;
		{ <$generic:ident as $trait:path>::$trait_type:ident $(,)? { $( $events:tt )* } };
		{$( $parsed:tt)*};
	) => {
		$crate::__decl_generic_event!(@generate
			$( #[ $attr ] )*;
			$event_generic_param;
			$($instance $( = $event_default_instance)? )?;
			{ $($events)* };
			{ $($parsed)*, $trait_type = <$generic as $trait>::$trait_type };
		);
	};
	// Finish formatting on a named one
	(@format_generic
		$(#[$attr:meta])*;
		$event_generic_param:ident;
		$($instance:ident $( = $event_default_instance:path)? )?;
		{ $generic_rename:ident = $generic_type:ty $(,)? { $( $events:tt )* } };
		{ $($parsed:tt)* };
	) => {
		$crate::__decl_generic_event!(@generate
			$(#[$attr])*;
			$event_generic_param;
			$($instance $( = $event_default_instance)? )?;
			{ $($events)* };
			{ $($parsed)*, $generic_rename = $generic_type };
		);
	};
	// Parse named
	(@format_generic
		$(#[$attr:meta])*;
		$event_generic_param:ident;
		$($instance:ident $( = $event_default_instance:path)? )?;
		{ $generic_rename:ident = $generic_type:ty, $($rest:tt)* };
		{$( $parsed:tt)*};
	) => {
		$crate::__decl_generic_event!(@format_generic
			$( #[ $attr ] )*;
			$event_generic_param;
			$( $instance $( = $event_default_instance)? )?;
			{ $($rest)* };
			{ $($parsed)*, $generic_rename = $generic_type };
		);
	};
	// Parse unnamed
	(@format_generic
		$(#[$attr:meta])*;
		$event_generic_param:ident;
		$($instance:ident $( = $event_default_instance:path)? )?;
		{ <$generic:ident as $trait:path>::$trait_type:ident, $($rest:tt)* };
		{$($parsed:tt)*};
	) => {
		$crate::__decl_generic_event!(@format_generic
			$( #[ $attr ] )*;
			$event_generic_param;
			$($instance $( = $event_default_instance)? )?;
			{ $($rest)* };
			{ $($parsed)*, $trait_type = <$generic as $trait>::$trait_type };
		);
	};
	// Unnamed type can't be parsed
	(@format_generic
		$(#[$attr:meta])*;
		$event_generic_param:ident;
		$($instance:ident $( = $event_default_instance:path)? )?;
		{ $generic_type:ty, $($rest:tt)* };
		{ $($parsed:tt)* };
	) => {
		$crate::__decl_generic_event!(@cannot_parse $generic_type);
	};
	// Final unnamed type can't be parsed
	(@format_generic
		$(#[$attr:meta])*;
		$event_generic_param:ident;
		$($instance:ident $( = $event_default_instance:path)? )?;
		{ $generic_type:ty { $( $events:tt )* } };
		{$( $parsed:tt)*};
	) => {
		$crate::__decl_generic_event!(@cannot_parse $generic_type);
	};
	(@generate
		$(#[$attr:meta])*;
		$event_generic_param:ident;
		$($instance:ident $( = $event_default_instance:path)? )?;
		{ $( $events:tt )* };
		{ ,$( $generic_param:ident = $generic_type:ty ),* };
	) => {
		/// [`RawEvent`] specialized for the configuration [`Trait`]
		///
		/// [`RawEvent`]: enum.RawEvent.html
		/// [`Trait`]: trait.Trait.html
		pub type Event<$event_generic_param $(, $instance $( = $event_default_instance)? )?> = RawEvent<$( $generic_type ),* $(, $instance)? >;

		#[derive(
			Clone, PartialEq, Eq,
			$crate::codec::Encode,
			$crate::codec::Decode,
			$crate::RuntimeDebug,
		)]
		/// Events for this module.
		///
		$(#[$attr])*
		pub enum RawEvent<$( $generic_param ),* $(, $instance)? > {
			$(
				$events
			)*
			$(
				#[doc(hidden)]
				#[codec(skip)]
				PhantomData($crate::sp_std::marker::PhantomData<$instance>),
			)?
		}
		impl<$( $generic_param ),* $(, $instance)? > From<RawEvent<$( $generic_param ),* $(, $instance)?>> for () {
			fn from(_: RawEvent<$( $generic_param ),* $(, $instance)?>) -> () { () }
		}
		impl<$( $generic_param ),* $(, $instance)?> RawEvent<$( $generic_param ),* $(, $instance)?> {
			#[allow(dead_code)]
			#[doc(hidden)]
			pub fn metadata() -> &'static [$crate::event::EventMetadata] {
				$crate::__events_to_metadata!(; $( $events )* )
			}
		}
	};
	(@cannot_parse $ty:ty) => {
		compile_error!(concat!("The type `", stringify!($ty), "` can't be parsed as an unnamed one, please name it `Name = ", stringify!($ty), "`"));
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __events_to_metadata {
	(
		$( $metadata:expr ),*;
		$( #[doc = $doc_attr:tt] )*
		$event:ident $( ( $( $param:path ),* $(,)? ) )*,
		$( $rest:tt )*
	) => {
		$crate::__events_to_metadata!(
			$( $metadata, )*
			$crate::event::EventMetadata {
				name: $crate::event::DecodeDifferent::Encode(stringify!($event)),
				arguments: $crate::event::DecodeDifferent::Encode(&[
					$( $( stringify!($param) ),* )*
				]),
				documentation: $crate::event::DecodeDifferent::Encode(&[
					$( $doc_attr ),*
				]),
			};
			$( $rest )*
		)
	};
	(
		$( $metadata:expr ),*;
	) => {
		&[ $( $metadata ),* ]
	}
}

/// Constructs an Event type for a runtime. This is usually called automatically by the
/// construct_runtime macro.
#[macro_export]
macro_rules! impl_outer_event {
	// Macro transformations (to convert invocations with incomplete parameters to the canonical
	// form)
	(
		$(#[$attr:meta])*
		pub enum $name:ident for $runtime:ident {
			$( $rest_events:tt )*
		}
	) => {
		$crate::impl_outer_event!(
			$( #[$attr] )*;
			$name;
			$runtime;
			Modules { $( $rest_events )* };
			{};
		);
	};
	// Generic + Instance
	(
		$(#[$attr:meta])*;
		$name:ident;
		$runtime:ident;
		Modules {
			$( #[codec(index = $index:tt)] )? $module:ident $instance:ident<T>,
			$( $rest_event_generic_instance:tt )*
		};
		{ $( $parsed:tt )* };
	) => {
		$crate::impl_outer_event!(
			$( #[$attr] )*;
			$name;
			$runtime;
			Modules { $( $rest_event_generic_instance )* };
			{ $( $parsed )* $module::Event<$runtime>{ $instance } index { $( $index )? }, };
		);
	};
	// Instance
	(
		$(#[$attr:meta])*;
		$name:ident;
		$runtime:ident;
		Modules {
			$( #[codec(index = $index:tt)] )? $module:ident $instance:ident,
			$( $rest_event_instance:tt )*
		};
		{ $( $parsed:tt )* };
	) => {
		$crate::impl_outer_event!(
			$( #[$attr] )*;
			$name;
			$runtime;
			Modules { $( $rest_event_instance )* };
			{ $( $parsed )* $module::Event { $instance } index { $( $index )? }, };
		);
	};
	// Generic
	(
		$(#[$attr:meta])*;
		$name:ident;
		$runtime:ident;
		Modules {
			$( #[codec(index = $index:tt)] )? $module:ident<T>,
			$( $rest_event_generic:tt )*
		};
		{ $( $parsed:tt )* };
	) => {
		$crate::impl_outer_event!(
			$( #[$attr] )*;
			$name;
			$runtime;
			Modules { $( $rest_event_generic )* };
			{ $( $parsed )* $module::Event<$runtime> index { $( $index )? }, };
		);
	};
	// No Generic and no Instance
	(
		$(#[$attr:meta])*;
		$name:ident;
		$runtime:ident;
		Modules {
			$( #[codec(index = $index:tt)] )? $module:ident,
			$( $rest_event_no_generic_no_instance:tt )*
		};
		{ $( $parsed:tt )* };
	) => {
		$crate::impl_outer_event!(
			$( #[$attr] )*;
			$name;
			$runtime;
			Modules { $( $rest_event_no_generic_no_instance )* };
			{ $( $parsed )* $module::Event index { $( $index )? }, };
		);
	};

	// The main macro expansion that actually renders the Event enum code.
	(
		$(#[$attr:meta])*;
		$name:ident;
		$runtime:ident;
		Modules {};
		{
			$(
				$module_name:ident::Event
				$( <$generic_param:ident> )?
				$( { $generic_instance:ident } )?
				index { $( $index:tt )? },
			)*
		};
	) => {
		$crate::paste::item! {
			#[derive(
				Clone, PartialEq, Eq,
				$crate::codec::Encode,
				$crate::codec::Decode,
				$crate::RuntimeDebug,
			)]
			$(#[$attr])*
			#[allow(non_camel_case_types)]
			pub enum $name {
				$(
					$( #[codec(index = $index)] )?
					[< $module_name $(_ $generic_instance )? >](
						$module_name::Event < $( $generic_param )? $(, $module_name::$generic_instance )? >
					),
				)*
			}
			$(
				impl From<$module_name::Event < $( $generic_param, )? $( $module_name::$generic_instance )? >> for $name {
					fn from(x: $module_name::Event < $( $generic_param, )? $( $module_name::$generic_instance )? >) -> Self {
						$name::[< $module_name $(_ $generic_instance )? >](x)
					}
				}
				impl $crate::sp_std::convert::TryInto<
					$module_name::Event < $( $generic_param, )? $( $module_name::$generic_instance )? >
				> for $name {
					type Error = ();

					fn try_into(self) -> $crate::sp_std::result::Result<
						$module_name::Event < $( $generic_param, )? $( $module_name::$generic_instance )? >, Self::Error
					> {
						match self {
							Self::[< $module_name $(_ $generic_instance )? >](evt) => Ok(evt),
							_ => Err(()),
						}
					}
				}
			)*
		}
		$crate::__impl_outer_event_json_metadata!(
			$runtime;
			$name;
			$(
				$module_name::Event
				< $( $generic_param )? $(, $module_name::$generic_instance )? >
				$( $generic_instance )?,
			)*;
		);
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __impl_outer_event_json_metadata {
	(
		$runtime:ident;
		$event_name:ident;
		$( $module_name:ident::Event < $( $generic_params:path ),* > $( $instance:ident )?, )*;
	) => {
		impl $runtime {
			#[allow(dead_code)]
			pub fn outer_event_metadata() -> $crate::event::OuterEventMetadata {
				$crate::event::OuterEventMetadata {
					name: $crate::event::DecodeDifferent::Encode(stringify!($event_name)),
					events: $crate::event::DecodeDifferent::Encode(&[
						$(
							(
								stringify!($module_name),
								$crate::event::FnEncode(
									$module_name::Event ::< $( $generic_params ),* > ::metadata
								)
							)
						),*
					])
				}
			}

			$crate::__impl_outer_event_json_metadata! {
				@DECL_MODULE_EVENT_FNS
				$( $module_name < $( $generic_params ),* > $( $instance )? ; )*
			}
		}
	};

	(@DECL_MODULE_EVENT_FNS
		$(
			$module_name:ident < $( $generic_params:path ),* > $( $instance:ident )? ;
		)*
	) => {
		$crate::paste::item! {
			$(
				#[allow(dead_code)]
				pub fn [< __module_events_ $module_name $( _ $instance )? >] () ->
					&'static [$crate::event::EventMetadata]
				{
					$module_name::Event ::< $( $generic_params ),* > ::metadata()
				}
			)*
		}
	}
}

#[cfg(test)]
#[allow(dead_code)]
mod tests {
	use super::*;
	use serde::Serialize;
	use codec::{Encode, Decode};

	mod system {
		pub trait Trait: 'static {
			type Origin;
			type BlockNumber;
			type PalletInfo: crate::traits::PalletInfo;
			type DbWeight: crate::traits::Get<crate::weights::RuntimeDbWeight>;
		}

		decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin, system=self {}
		}

		decl_event!(
			pub enum Event {
				SystemEvent,
			}
		);
	}

	mod system_renamed {
		pub trait Trait: 'static {
			type Origin;
			type BlockNumber;
			type PalletInfo: crate::traits::PalletInfo;
			type DbWeight: crate::traits::Get<crate::weights::RuntimeDbWeight>;
		}

		decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin, system=self {}
		}

		decl_event!(
			pub enum Event {
				SystemEvent,
			}
		);
	}

	mod event_module {
		use super::system;

		pub trait Trait: system::Trait {
			type Balance;
		}

		decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin, system=system {}
		}

		decl_event!(
			/// Event without renaming the generic parameter `Balance` and `Origin`.
			pub enum Event<T> where <T as Trait>::Balance, <T as system::Trait>::Origin
			{
				/// Hi, I am a comment.
				TestEvent(Balance, Origin),
				/// Dog
				EventWithoutParams,
			}
		);
	}

	mod event_module2 {
		use super::system;

		pub trait Trait: system::Trait {
			type Balance;
		}

		decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin, system=system {}
		}

		decl_event!(
			/// Event with renamed generic parameter
			pub enum Event<T> where
				BalanceRenamed = <T as Trait>::Balance,
				OriginRenamed = <T as system::Trait>::Origin
			{
				TestEvent(BalanceRenamed),
				TestOrigin(OriginRenamed),
			}
		);
	}

	mod event_module3 {
		decl_event!(
			pub enum Event {
				HiEvent,
			}
		);
	}

	mod event_module4 {
		use super::system;

		pub trait Trait: system::Trait {
			type Balance;
		}

		decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin, system=system {}
		}

		decl_event!(
			/// Event finish formatting on an unnamed one with trailing comma
			pub enum Event<T> where
				<T as Trait>::Balance,
				<T as system::Trait>::Origin,
			{
				TestEvent(Balance, Origin),
			}
		);
	}

	mod event_module5 {
		use super::system;

		pub trait Trait: system::Trait {
			type Balance;
		}

		decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin, system=system {}
		}

		decl_event!(
			/// Event finish formatting on an named one with trailing comma
			pub enum Event<T> where
				BalanceRenamed = <T as Trait>::Balance,
				OriginRenamed = <T as system::Trait>::Origin,
			{
				TestEvent(BalanceRenamed, OriginRenamed),
				TrailingCommaInArgs(
					u32,
					u32,
				),
			}
		);
	}

	#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, Serialize)]
	pub struct TestRuntime;

	impl_outer_event! {
		pub enum TestEvent for TestRuntime {
			system,
			event_module<T>,
			event_module2<T>,
			event_module3,
		}
	}

	#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, Serialize)]
	pub struct TestRuntime2;

	impl_outer_event! {
		pub enum TestEventSystemRenamed for TestRuntime2 {
			system_renamed,
			event_module<T>,
			#[codec(index = "5")] event_module2<T>,
			event_module3,
		}
	}

	impl event_module::Trait for TestRuntime {
		type Balance = u32;
	}

	impl event_module2::Trait for TestRuntime {
		type Balance = u32;
	}

	impl system::Trait for TestRuntime {
		type Origin = u32;
		type BlockNumber = u32;
		type PalletInfo = ();
		type DbWeight = ();
	}

	impl event_module::Trait for TestRuntime2 {
		type Balance = u32;
	}

	impl event_module2::Trait for TestRuntime2 {
		type Balance = u32;
	}

	impl system_renamed::Trait for TestRuntime2 {
		type Origin = u32;
		type BlockNumber = u32;
		type PalletInfo = ();
		type DbWeight = ();
	}

	impl system::Trait for TestRuntime2 {
		type Origin = u32;
		type BlockNumber = u32;
		type PalletInfo = ();
		type DbWeight = ();
	}

	const EXPECTED_METADATA: OuterEventMetadata = OuterEventMetadata {
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
						arguments: DecodeDifferent::Encode(&[ "Balance", "Origin" ]),
						documentation: DecodeDifferent::Encode(&[ " Hi, I am a comment." ])
					},
					EventMetadata {
						name: DecodeDifferent::Encode("EventWithoutParams"),
						arguments: DecodeDifferent::Encode(&[]),
						documentation: DecodeDifferent::Encode(&[ " Dog" ]),
					},
				])
			),
			(
				"event_module2",
				FnEncode(|| &[
					EventMetadata {
						name: DecodeDifferent::Encode("TestEvent"),
						arguments: DecodeDifferent::Encode(&[ "BalanceRenamed" ]),
						documentation: DecodeDifferent::Encode(&[])
					},
					EventMetadata {
						name: DecodeDifferent::Encode("TestOrigin"),
						arguments: DecodeDifferent::Encode(&[ "OriginRenamed" ]),
						documentation: DecodeDifferent::Encode(&[]),
					},
				])
			),
			(
				"event_module3",
				FnEncode(|| &[
					EventMetadata {
						name: DecodeDifferent::Encode("HiEvent"),
						arguments: DecodeDifferent::Encode(&[]),
						documentation: DecodeDifferent::Encode(&[])
					}
				])
			)
		])
	};

	#[test]
	fn outer_event_metadata() {
		assert_eq!(EXPECTED_METADATA, TestRuntime::outer_event_metadata());
	}

	#[test]
	fn test_codec() {
		let runtime_1_event_module_2 = TestEvent::event_module2(
			event_module2::Event::<TestRuntime>::TestEvent(3)
		);
		assert_eq!(runtime_1_event_module_2.encode()[0], 2);

		let runtime_2_event_module_2 = TestEventSystemRenamed::event_module2(
			event_module2::Event::<TestRuntime2>::TestEvent(3)
		);
		assert_eq!(runtime_2_event_module_2.encode()[0], 5);
		
		let runtime_2_event_module_3 = TestEventSystemRenamed::event_module3(
			event_module3::Event::HiEvent
		);
		assert_eq!(runtime_2_event_module_3.encode()[0], 3);
	}
}
