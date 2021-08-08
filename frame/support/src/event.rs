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

//! Macros that define an Event types. Events can be used to easily report changes or conditions
//! in your runtime to external entities like users, chain explorers, or dApps.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

pub use frame_metadata::{DecodeDifferent, EventMetadata, FnEncode, OuterEventMetadata};

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
/// # fn main() {}
/// ```
///
/// # Generic Event Example:
///
/// ```rust
/// trait Config {
///     type Balance;
///     type Token;
/// }
///
/// mod event1 {
///     // Event that specifies the generic parameter explicitly (`Balance`).
///     frame_support::decl_event!(
///        pub enum Event<T> where Balance = <T as super::Config>::Balance {
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
///        pub enum Event<T> where <T as super::Config>::Balance {
///           Message(Balance),
///        }
///     );
/// }
///
/// mod event3 {
///     // And we even support declaring multiple generic parameters!
///     frame_support::decl_event!(
///        pub enum Event<T> where <T as super::Config>::Balance, <T as super::Config>::Token {
///           Message(Balance, Token),
///        }
///     );
/// }
///
/// # fn main() {}
/// ```
///
/// The syntax for generic events requires the `where`.
///
/// # Generic Event with Instance Example:
///
/// ```rust
/// # struct DefaultInstance;
/// # trait Instance {}
/// # impl Instance for DefaultInstance {}
/// trait Config<I: Instance=DefaultInstance> {
///     type Balance;
///     type Token;
/// }
///
/// // For module with instances, DefaultInstance is optional
/// frame_support::decl_event!(
///    pub enum Event<T, I: Instance = DefaultInstance> where
///       <T as Config>::Balance,
///       <T as Config>::Token
///    {
///       Message(Balance, Token),
///    }
/// );
/// # fn main() {}
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
		/// [`RawEvent`] specialized for the configuration [`Config`]
		///
		/// [`RawEvent`]: enum.RawEvent.html
		/// [`Config`]: trait.Config.html
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

#[cfg(test)]
#[allow(dead_code)]
mod tests {
	use super::*;
	use codec::{Decode, Encode};
	use serde::Serialize;

	mod system {
		pub trait Config: 'static {
			type Origin;
			type BlockNumber;
			type PalletInfo: crate::traits::PalletInfo;
			type DbWeight: crate::traits::Get<crate::weights::RuntimeDbWeight>;
		}

		decl_module! {
			pub struct Module<T: Config> for enum Call where origin: T::Origin, system=self {}
		}

		decl_event!(
			pub enum Event {
				SystemEvent,
			}
		);
	}

	mod system_renamed {
		pub trait Config: 'static {
			type Origin;
			type BlockNumber;
			type PalletInfo: crate::traits::PalletInfo;
			type DbWeight: crate::traits::Get<crate::weights::RuntimeDbWeight>;
		}

		decl_module! {
			pub struct Module<T: Config> for enum Call where origin: T::Origin, system=self {}
		}

		decl_event!(
			pub enum Event {
				SystemEvent,
			}
		);
	}

	mod event_module {
		use super::system;

		pub trait Config: system::Config {
			type Balance;
		}

		decl_module! {
			pub struct Module<T: Config> for enum Call where origin: T::Origin, system=system {}
		}

		decl_event!(
			/// Event without renaming the generic parameter `Balance` and `Origin`.
			pub enum Event<T> where <T as Config>::Balance, <T as system::Config>::Origin
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

		pub trait Config: system::Config {
			type Balance;
		}

		decl_module! {
			pub struct Module<T: Config> for enum Call where origin: T::Origin, system=system {}
		}

		decl_event!(
			/// Event with renamed generic parameter
			pub enum Event<T>
			where
				BalanceRenamed = <T as Config>::Balance,
				OriginRenamed = <T as system::Config>::Origin,
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

		pub trait Config: system::Config {
			type Balance;
		}

		decl_module! {
			pub struct Module<T: Config> for enum Call where origin: T::Origin, system=system {}
		}

		decl_event!(
			/// Event finish formatting on an unnamed one with trailing comma
			pub enum Event<T> where
				<T as Config>::Balance,
				<T as system::Config>::Origin,
			{
				TestEvent(Balance, Origin),
			}
		);
	}

	mod event_module5 {
		use super::system;

		pub trait Config: system::Config {
			type Balance;
		}

		decl_module! {
			pub struct Module<T: Config> for enum Call where origin: T::Origin, system=system {}
		}

		decl_event!(
			/// Event finish formatting on an named one with trailing comma
			pub enum Event<T>
			where
				BalanceRenamed = <T as Config>::Balance,
				OriginRenamed = <T as system::Config>::Origin,
			{
				TestEvent(BalanceRenamed, OriginRenamed),
				TrailingCommaInArgs(u32, u32),
			}
		);
	}

	#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, Serialize)]
	pub struct TestRuntime;

	#[derive(Debug, Clone, PartialEq, Eq, Encode, Decode, Serialize)]
	pub struct TestRuntime2;

	impl event_module::Config for TestRuntime {
		type Balance = u32;
	}

	impl event_module2::Config for TestRuntime {
		type Balance = u32;
	}

	impl system::Config for TestRuntime {
		type Origin = u32;
		type BlockNumber = u32;
		type PalletInfo = crate::tests::PanicPalletInfo;
		type DbWeight = ();
	}

	#[test]
	fn event_metadata() {
		assert_eq!(
			system_renamed::Event::metadata(),
			&[EventMetadata {
				name: DecodeDifferent::Encode("SystemEvent"),
				arguments: DecodeDifferent::Encode(&[]),
				documentation: DecodeDifferent::Encode(&[]),
			},]
		);
		assert_eq!(
			event_module::Event::<TestRuntime>::metadata(),
			&[
				EventMetadata {
					name: DecodeDifferent::Encode("TestEvent"),
					arguments: DecodeDifferent::Encode(&["Balance", "Origin"]),
					documentation: DecodeDifferent::Encode(&[" Hi, I am a comment."])
				},
				EventMetadata {
					name: DecodeDifferent::Encode("EventWithoutParams"),
					arguments: DecodeDifferent::Encode(&[]),
					documentation: DecodeDifferent::Encode(&[" Dog"]),
				},
			]
		);
		assert_eq!(
			event_module2::Event::<TestRuntime>::metadata(),
			&[
				EventMetadata {
					name: DecodeDifferent::Encode("TestEvent"),
					arguments: DecodeDifferent::Encode(&["BalanceRenamed"]),
					documentation: DecodeDifferent::Encode(&[])
				},
				EventMetadata {
					name: DecodeDifferent::Encode("TestOrigin"),
					arguments: DecodeDifferent::Encode(&["OriginRenamed"]),
					documentation: DecodeDifferent::Encode(&[]),
				},
			]
		);
		assert_eq!(
			event_module3::Event::metadata(),
			&[EventMetadata {
				name: DecodeDifferent::Encode("HiEvent"),
				arguments: DecodeDifferent::Encode(&[]),
				documentation: DecodeDifferent::Encode(&[])
			}],
		);
	}
}
