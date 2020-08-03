// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

//! Macros that define an Origin type. Every function call to your runtime has an origin which
//! specifies where the extrinsic was generated from.

/// Constructs an Origin type for a runtime. This is usually called automatically by the
/// construct_runtime macro. See also __create_decl_macro.
#[macro_export]
macro_rules! impl_outer_origin {

	// Macro transformations (to convert invocations with incomplete parameters to the canonical
	// form)
	(
		$(#[$attr:meta])*
		pub enum $name:ident for $runtime:ident {
			$( $rest_without_system:tt )*
		}
	) => {
		$crate::impl_outer_origin! {
			$(#[$attr])*
			pub enum $name for $runtime where system = frame_system {
				$( $rest_without_system )*
			}
		}
	};

	(
		$(#[$attr:meta])*
		pub enum $name:ident for $runtime:ident where system = $system:ident {
			$( $rest_with_system:tt )*
		}
	) => {
		$crate::paste::item! {
			$crate::impl_outer_origin!(
				$( #[$attr] )*;
				$name;
				[< $name Caller >];
				$runtime;
				$system;
				Modules { $( $rest_with_system )* };
			);
		}
	};

	// Generic + Instance
	(
		$(#[$attr:meta])*;
		$name:ident;
		$caller_name:ident;
		$runtime:ident;
		$system:ident;
		Modules {
			$module:ident $instance:ident <T>
			$(, $( $rest_module:tt )* )?
		};
		$( $parsed:tt )*
	) => {
		$crate::impl_outer_origin!(
			$( #[$attr] )*;
			$name;
			$caller_name;
			$runtime;
			$system;
			Modules { $( $( $rest_module )* )? };
			$( $parsed )* $module <$runtime> { $instance },
		);
	};

	// Instance
	(
		$(#[$attr:meta])*;
		$name:ident;
		$caller_name:ident;
		$runtime:ident;
		$system:ident;
		Modules {
			$module:ident $instance:ident
			$(, $rest_module:tt )*
		};
		$( $parsed:tt )*
	) => {
		$crate::impl_outer_origin!(
			$( #[$attr] )*;
			$name;
			$caller_name;
			$runtime;
			$system;
			Modules { $( $rest_module )* };
			$( $parsed )* $module { $instance },
		);
	};

	// Generic
	(
		$(#[$attr:meta])*;
		$name:ident;
		$caller_name:ident;
		$runtime:ident;
		$system:ident;
		Modules {
			$module:ident <T>
			$(, $( $rest_module:tt )* )?
		};
		$( $parsed:tt )*
	) => {
		$crate::impl_outer_origin!(
			$( #[$attr] )*;
			$name;
			$caller_name;
			$runtime;
			$system;
			Modules { $( $( $rest_module )* )? };
			$( $parsed )* $module <$runtime>,
		);
	};

	// No Generic and no Instance
	(
		$(#[$attr:meta])*;
		$name:ident;
		$caller_name:ident;
		$runtime:ident;
		$system:ident;
		Modules {
			$module:ident
			$(, $( $rest_module:tt )* )?
		};
		$( $parsed:tt )*
	) => {
		$crate::impl_outer_origin!(
			$( #[$attr] )*;
			$name;
			$caller_name;
			$runtime;
			$system;
			Modules { $( $( $rest_module )* )? };
			$( $parsed )* $module,
		);
	};

	// The main macro expansion that actually renders the Origin enum code.
	(
		$(#[$attr:meta])*;
		$name:ident;
		$caller_name:ident;
		$runtime:ident;
		$system:ident;
		Modules { };
		$( $module:ident $( < $generic:ident > )? $( { $generic_instance:ident } )? ,)*
	) => {
		// WARNING: All instance must hold the filter `frame_system::Trait::BaseCallFilter`, except
		// when caller is system Root. One can use `OriginTrait::reset_filter` to do so.
		#[derive(Clone)]
		pub struct $name {
			caller: $caller_name,
			filter: $crate::sp_std::rc::Rc<Box<dyn Fn(&<$runtime as $system::Trait>::Call) -> bool>>,
		}

		#[cfg(not(feature = "std"))]
		impl $crate::sp_std::fmt::Debug for $name {
			fn fmt(
				&self,
				fmt: &mut $crate::sp_std::fmt::Formatter
			) -> $crate::sp_std::result::Result<(), $crate::sp_std::fmt::Error> {
				fmt.write_str("<wasm:stripped>")
			}
		}

		#[cfg(feature = "std")]
		impl $crate::sp_std::fmt::Debug for $name {
			fn fmt(
				&self,
				fmt: &mut $crate::sp_std::fmt::Formatter
			) -> $crate::sp_std::result::Result<(), $crate::sp_std::fmt::Error> {
				fmt.debug_struct(stringify!($name))
					.field("caller", &self.caller)
					.field("filter", &"[function ptr]")
					.finish()
			}
		}

		impl $crate::traits::OriginTrait for $name {
			type Call = <$runtime as $system::Trait>::Call;
			type PalletsOrigin = $caller_name;

			fn add_filter(&mut self, filter: impl Fn(&Self::Call) -> bool + 'static) {
				let f = self.filter.clone();

				self.filter = $crate::sp_std::rc::Rc::new(Box::new(move |call| {
					f(call) && filter(call)
				}));
			}

			fn reset_filter(&mut self) {
				let filter = <
					<$runtime as $system::Trait>::BaseCallFilter
					as $crate::traits::Filter<<$runtime as $system::Trait>::Call>
				>::filter;

				self.filter = $crate::sp_std::rc::Rc::new(Box::new(filter));
			}

			fn set_caller_from(&mut self, other: impl Into<Self>) {
				self.caller = other.into().caller
			}

			fn filter_call(&self, call: &Self::Call) -> bool {
				(self.filter)(call)
			}

			fn caller(&self) -> &Self::PalletsOrigin {
				&self.caller
			}
		}

		$crate::paste::item! {
			#[derive(Clone, PartialEq, Eq, $crate::RuntimeDebug, $crate::codec::Encode, $crate::codec::Decode)]
			$(#[$attr])*
			#[allow(non_camel_case_types)]
			pub enum $caller_name {
				system($system::Origin<$runtime>),
				$(
					[< $module $( _ $generic_instance )? >]
					($module::Origin < $( $generic, )? $( $module::$generic_instance )? > ),
				)*
				#[allow(dead_code)]
				Void($crate::Void)
			}
		}

		#[allow(dead_code)]
		impl $name {
			/// Create with system none origin and `frame-system::Trait::BaseCallFilter`.
			pub fn none() -> Self {
				$system::RawOrigin::None.into()
			}
			/// Create with system root origin and no filter.
			pub fn root() -> Self {
				$system::RawOrigin::Root.into()
			}
			/// Create with system signed origin and `frame-system::Trait::BaseCallFilter`.
			pub fn signed(by: <$runtime as $system::Trait>::AccountId) -> Self {
				$system::RawOrigin::Signed(by).into()
			}
		}

		impl From<$system::Origin<$runtime>> for $caller_name {
			fn from(x: $system::Origin<$runtime>) -> Self {
				$caller_name::system(x)
			}
		}
		impl From<$system::Origin<$runtime>> for $name {
			/// Convert to runtime origin:
			/// * root origin is built with no filter
			/// * others use `frame-system::Trait::BaseCallFilter`
			fn from(x: $system::Origin<$runtime>) -> Self {
				let o: $caller_name = x.into();
				o.into()
			}
		}

		impl From<$caller_name> for $name {
			fn from(x: $caller_name) -> Self {
				let mut o = $name {
					caller: x,
					filter: $crate::sp_std::rc::Rc::new(Box::new(|_| true)),
				};

				// Root has no filter
				if !matches!(o.caller, $caller_name::system($system::Origin::<$runtime>::Root)) {
					$crate::traits::OriginTrait::reset_filter(&mut o);
				}

				o
			}
		}

		impl Into<$crate::sp_std::result::Result<$system::Origin<$runtime>, $name>> for $name {
			/// NOTE: converting to pallet origin loses the origin filter information.
			fn into(self) -> $crate::sp_std::result::Result<$system::Origin<$runtime>, Self> {
				if let $caller_name::system(l) = self.caller {
					Ok(l)
				} else {
					Err(self)
				}
			}
		}
		impl From<Option<<$runtime as $system::Trait>::AccountId>> for $name {
			/// Convert to runtime origin with caller being system signed or none and use filter
			/// `frame-system::Trait::BaseCallFilter`.
			fn from(x: Option<<$runtime as $system::Trait>::AccountId>) -> Self {
				<$system::Origin<$runtime>>::from(x).into()
			}
		}

		$(
			$crate::paste::item! {
				impl From<$module::Origin < $( $generic )? $(, $module::$generic_instance )? > > for $caller_name {
					fn from(x: $module::Origin < $( $generic )? $(, $module::$generic_instance )? >) -> Self {
						$caller_name::[< $module $( _ $generic_instance )? >](x)
					}
				}

				impl From<$module::Origin < $( $generic )? $(, $module::$generic_instance )? > > for $name {
					/// Convert to runtime origin using `frame-system::Trait::BaseCallFilter`.
					fn from(x: $module::Origin < $( $generic )? $(, $module::$generic_instance )? >) -> Self {
						let x: $caller_name = x.into();
						x.into()
					}
				}
				impl Into<
					$crate::sp_std::result::Result<
						$module::Origin < $( $generic )? $(, $module::$generic_instance )? >,
						$name,
					>>
				for $name {
					/// NOTE: converting to pallet origin loses the origin filter information.
					fn into(self) -> $crate::sp_std::result::Result<
						$module::Origin < $( $generic )? $(, $module::$generic_instance )? >,
						Self,
					> {
						if let $caller_name::[< $module $( _ $generic_instance )? >](l) = self.caller {
							Ok(l)
						} else {
							Err(self)
						}
					}
				}
			}
		)*
	}
}

#[cfg(test)]
mod tests {
	use codec::{Encode, Decode};
	use crate::traits::{Filter, OriginTrait};
	mod frame_system {
		use super::*;

		pub trait Trait {
			type AccountId;
			type Call;
			type BaseCallFilter;
		}

		#[derive(Clone, PartialEq, Eq, Debug, Encode, Decode)]
		pub enum RawOrigin<AccountId> {
			Root,
			Signed(AccountId),
			None,
		}

		impl<AccountId> From<Option<AccountId>> for RawOrigin<AccountId> {
			fn from(s: Option<AccountId>) -> RawOrigin<AccountId> {
				match s {
					Some(who) => RawOrigin::Signed(who),
					None => RawOrigin::None,
				}
			}
		}

		pub type Origin<T> = RawOrigin<<T as Trait>::AccountId>;
	}

	mod origin_without_generic {
		use super::*;

		#[derive(Clone, PartialEq, Eq, Debug, Encode, Decode)]
		pub struct Origin;
	}

	mod origin_with_generic {
		use super::*;

		#[derive(Clone, PartialEq, Eq, Debug, Encode, Decode)]
		pub struct Origin<T> {
			t: T
		}
	}

	#[derive(Clone, PartialEq, Eq, Debug, Encode, Decode)]
	pub struct TestRuntime;

	pub struct BaseCallFilter;
	impl Filter<u32> for BaseCallFilter {
		fn filter(c: &u32) -> bool {
			*c % 2 == 0
		}
	}

	impl frame_system::Trait for TestRuntime {
		type AccountId = u32;
		type Call = u32;
		type BaseCallFilter = BaseCallFilter;
	}

	impl_outer_origin!(
		pub enum OriginWithoutSystem for TestRuntime {
			origin_without_generic,
			origin_with_generic<T>,
		}
	);

	impl_outer_origin!(
		pub enum OriginWithoutSystem2 for TestRuntime {
			origin_with_generic<T>,
			origin_without_generic
		}
	);

	impl_outer_origin!(
		pub enum OriginWithSystem for TestRuntime where system = frame_system {
			origin_without_generic,
			origin_with_generic<T>
		}
	);

	impl_outer_origin!(
		pub enum OriginWithSystem2 for TestRuntime where system = frame_system {
			origin_with_generic<T>,
			origin_without_generic,
		}
	);

	impl_outer_origin!(
		pub enum OriginEmpty for TestRuntime where system = frame_system {}
	);

	#[test]
	fn test_default_filter() {
		assert_eq!(OriginWithSystem::root().filter_call(&0), true);
		assert_eq!(OriginWithSystem::root().filter_call(&1), true);
		assert_eq!(OriginWithSystem::none().filter_call(&0), true);
		assert_eq!(OriginWithSystem::none().filter_call(&1), false);
		assert_eq!(OriginWithSystem::signed(0).filter_call(&0), true);
		assert_eq!(OriginWithSystem::signed(0).filter_call(&1), false);
		assert_eq!(OriginWithSystem::from(Some(0)).filter_call(&0), true);
		assert_eq!(OriginWithSystem::from(Some(0)).filter_call(&1), false);
		assert_eq!(OriginWithSystem::from(None).filter_call(&0), true);
		assert_eq!(OriginWithSystem::from(None).filter_call(&1), false);
		assert_eq!(OriginWithSystem::from(origin_without_generic::Origin).filter_call(&0), true);
		assert_eq!(OriginWithSystem::from(origin_without_generic::Origin).filter_call(&1), false);

		let mut origin = OriginWithSystem::from(Some(0));

		origin.add_filter(|c| *c % 2 == 1);
		assert_eq!(origin.filter_call(&0), false);
		assert_eq!(origin.filter_call(&1), false);

		origin.set_caller_from(OriginWithSystem::root());
		assert!(matches!(origin.caller, OriginWithSystemCaller::system(frame_system::RawOrigin::Root)));
		assert_eq!(origin.filter_call(&0), false);
		assert_eq!(origin.filter_call(&1), false);

		origin.reset_filter();
		assert_eq!(origin.filter_call(&0), true);
		assert_eq!(origin.filter_call(&1), false);
	}
}
