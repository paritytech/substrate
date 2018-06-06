// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Dispatch system. Just dispatches calls.

pub use rstd::prelude::{Vec, Clone, Eq, PartialEq};
#[cfg(feature = "std")]
pub use std::fmt;
pub use rstd::result;
#[cfg(feature = "std")]
use serde;
pub use codec::{Slicable, Input};

pub type Result = result::Result<(), &'static str>;

pub trait Dispatchable {
	type Trait;
	fn dispatch(self) -> Result;
}

pub trait AuxDispatchable {
	type Aux;
	type Trait;
	fn dispatch(self, aux: &Self::Aux) -> Result;
}

#[cfg(feature = "std")]
pub trait AuxCallable {
	type Call: AuxDispatchable + Slicable + ::serde::Serialize + Clone + PartialEq + Eq;
}
#[cfg(not(feature = "std"))]
pub trait AuxCallable {
	type Call: AuxDispatchable + Slicable + Clone + PartialEq + Eq;
}

// dirty hack to work around serde_derive issue
// https://github.com/rust-lang/rust/issues/51331
pub type AuxCallableCallFor<A> = <A as AuxCallable>::Call;

#[cfg(feature = "std")]
pub trait Callable {
	type Call: Dispatchable + Slicable + ::serde::Serialize + Clone + PartialEq + Eq;
}
#[cfg(not(feature = "std"))]
pub trait Callable {
	type Call: Dispatchable + Slicable + Clone + PartialEq + Eq;
}

// dirty hack to work around serde_derive issue.
// https://github.com/rust-lang/rust/issues/51331
pub type CallableCallFor<C> = <C as Callable>::Call;

#[cfg(feature = "std")]
pub trait Parameter: Slicable + serde::Serialize + Clone + Eq + fmt::Debug {}

#[cfg(feature = "std")]
impl<T> Parameter for T where T: Slicable + serde::Serialize + Clone + Eq + fmt::Debug {}

#[cfg(not(feature = "std"))]
pub trait Parameter: Slicable + Clone + Eq {}

#[cfg(not(feature = "std"))]
impl<T> Parameter for T where T: Slicable + Clone + Eq {}

/// Declare a struct for this module, then implement dispatch logic to create a pairing of several
/// dispatch traits and enums.
#[macro_export]
macro_rules! decl_module {
	(
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>;
		$($rest:tt)*
	) => {
		// TODO: switching based on std feature is because of an issue in
		// serde-derive for when we attempt to derive `Deserialize` on these types,
		// in a situation where we've imported `substrate_runtime_support` as another name.
		#[cfg(feature = "std")]
		$(#[$attr])*
		pub struct $mod_type<$trait_instance: $trait_name>(::std::marker::PhantomData<$trait_instance>);

		#[cfg(not(feature = "std"))]
		$(#[$attr])*
		pub struct $mod_type<$trait_instance: $trait_name>(::core::marker::PhantomData<$trait_instance>);

		decl_dispatch! {
			impl for $mod_type<$trait_instance: $trait_name>;
			$($rest)*
		}
	};
	(
		$(#[$attr:meta])*
		struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>;
		$($rest:tt)*
	) => {
		#[cfg(feature = "std")]
		$(#[$attr])*
		struct $mod_type<$trait_instance: $trait_name>(::std::marker::PhantomData<$trait_instance>);

		#[cfg(not(feature = "std"))]
		$(#[$attr])*
		struct $mod_type<$trait_instance: $trait_name>(::core::marker::PhantomData<$trait_instance>);
		decl_dispatch! {
			impl for $mod_type<$trait_instance: $trait_name>;
			$($rest)*
		}
	}
}

/// Implement several dispatch modules to create a pairing of a dispatch trait and enum.
#[macro_export]
macro_rules! decl_dispatch {
	// WITHOUT AUX
	(
		impl for $mod_type:ident<$trait_instance:ident: $trait_name:ident>;
		$(#[$attr:meta])*
		pub enum $call_type:ident {
			$(
				fn $fn_name:ident(
					$(
						$param_name:ident : $param:ty
					),*
				) -> $result:ty
				= $id:expr ;
			)*
		}
		$($rest:tt)*
	) => {
		__decl_dispatch_module_without_aux! {
			impl for $mod_type<$trait_instance: $trait_name>;
			$(#[$attr])*
			pub enum $call_type;
			$(
				fn $fn_name( $( $param_name: $param ),* ) -> $result = $id;
			)*
		}
		decl_dispatch! {
			impl for $mod_type<$trait_instance: $trait_name>;
			$($rest)*
		}
	};
	// WITH AUX
	(
		impl for $mod_type:ident<$trait_instance:ident: $trait_name:ident>;
		$(#[$attr:meta])*
		pub enum $call_type:ident where aux: $aux_type:ty {
			$(
				fn $fn_name:ident(aux
					$(
						, $param_name:ident : $param:ty
					)*
				) -> $result:ty
				= $id:expr ;
			)*
		}
		$($rest:tt)*
	) => {
		__decl_dispatch_module_with_aux! {
			impl for $mod_type<$trait_instance: $trait_name>;
			$(#[$attr])*
			pub enum $call_type where aux: $aux_type;
			$(
				fn $fn_name(aux $(, $param_name: $param )*) -> $result = $id;
			)*
		}
		decl_dispatch! {
			impl for $mod_type<$trait_instance: $trait_name>;
			$($rest)*
		}
	};
	// BASE CASE
	(
		impl for $mod_type:ident<$trait_instance:ident: $trait_name:ident>;
	) => {
		impl<$trait_instance: $trait_name> $mod_type<$trait_instance> {
			pub fn aux_dispatch<D: $crate::dispatch::AuxDispatchable<Trait = $trait_instance>>(d: D, aux: &D::Aux) -> $crate::dispatch::Result {
				d.dispatch(aux)
			}
			pub fn dispatch<D: $crate::dispatch::Dispatchable<Trait = $trait_instance>>(d: D) -> $crate::dispatch::Result {
				d.dispatch()
			}
		}
	}
}

#[macro_export]
/// Implement a single dispatch modules to create a pairing of a dispatch trait and enum.
macro_rules! __decl_dispatch_module_without_aux {
	(
		impl for $mod_type:ident<$trait_instance:ident: $trait_name:ident>;
		$(#[$attr:meta])*
		pub enum $call_type:ident;
		$(
			fn $fn_name:ident(
				$(
					$param_name:ident : $param:ty
				),*
			)
			-> $result:ty
			= $id:expr ;
		)*
	) => {
		__decl_dispatch_module_common! {
			impl for $mod_type<$trait_instance: $trait_name>;
			$(#[$attr])*
			pub enum $call_type;
			$( fn $fn_name( $( $param_name : $param ),* ) -> $result = $id ; )*
		}
		impl<$trait_instance: $trait_name> $crate::dispatch::Dispatchable
			for $call_type<$trait_instance>
		{
			type Trait = $trait_instance;
			fn dispatch(self) -> $crate::dispatch::Result {
				match self {
					$(
						$call_type::$fn_name( $( $param_name ),* ) =>
							<$mod_type<$trait_instance>>::$fn_name( $( $param_name ),* ),
					)*
					$call_type::__PhantomItem(_) => { panic!("__PhantomItem should never be used.") },
				}
			}
		}
		impl<$trait_instance: $trait_name> $crate::dispatch::Callable
			for $mod_type<$trait_instance>
		{
			type Call = $call_type<$trait_instance>;
		}
	}
}

#[macro_export]
/// Implement a single dispatch modules to create a pairing of a dispatch trait and enum.
macro_rules! __decl_dispatch_module_with_aux {
	(
		impl for $mod_type:ident<$trait_instance:ident: $trait_name:ident>;
		$(#[$attr:meta])*
		pub enum $call_type:ident where aux: $aux_type:ty;
		$(
			fn $fn_name:ident(aux
				$(
					, $param_name:ident : $param:ty
				)*
			)
			-> $result:ty
			= $id:expr ;
		)*
	) => {
		__decl_dispatch_module_common! {
			impl for $mod_type<$trait_instance: $trait_name>;
			$(#[$attr])*
			pub enum $call_type;
			$( fn $fn_name( $( $param_name : $param ),* ) -> $result = $id ; )*
		}
		impl<$trait_instance: $trait_name> $crate::dispatch::AuxDispatchable
			for $call_type<$trait_instance>
		{
			type Trait = $trait_instance;
			type Aux = $aux_type;
			fn dispatch(self, aux: &Self::Aux) -> $crate::dispatch::Result {
				match self {
					$(
						$call_type::$fn_name( $( $param_name ),* ) =>
							<$mod_type<$trait_instance>>::$fn_name( aux $(, $param_name )* ),
					)*
					$call_type::__PhantomItem(_) => { panic!("__PhantomItem should never be used.") },
				}
			}
		}
		impl<$trait_instance: $trait_name> $crate::dispatch::AuxCallable
			for $mod_type<$trait_instance>
		{
			type Call = $call_type<$trait_instance>;
		}
	};
}

/// Implement a single dispatch modules to create a pairing of a dispatch trait and enum.
#[macro_export]
macro_rules! __decl_dispatch_module_common {
	(
		impl for $mod_type:ident<$trait_instance:ident: $trait_name:ident>;
		$(#[$attr:meta])*
		pub enum $call_type:ident;
		$(
			fn $fn_name:ident(
				$(
					$param_name:ident : $param:ty
				),*
			)
			-> $result:ty
			= $id:expr ;
		)*
	) => {
		#[cfg(feature = "std")]
		$(#[$attr])*
		pub enum $call_type<$trait_instance: $trait_name> {
			__PhantomItem(::std::marker::PhantomData<$trait_instance>),
			$(
				#[allow(non_camel_case_types)]
				$fn_name ( $( $param ),* ),
			)*
		}

		#[cfg(not(feature = "std"))]
		$(#[$attr])*
		pub enum $call_type<$trait_instance: $trait_name> {
			__PhantomItem(::core::marker::PhantomData<$trait_instance>),
			$(
				#[allow(non_camel_case_types)]
				$fn_name ( $( $param ),* ),
			)*
		}

		// manual implementation of clone/eq/partialeq because using derive erroneously requires
		// clone/eq/partialeq from T.
		impl<$trait_instance: $trait_name> $crate::dispatch::Clone
			for $call_type<$trait_instance>
		{
			fn clone(&self) -> Self {
				match *self {
					$(
						$call_type::$fn_name( $( ref $param_name ),* ) =>
							$call_type::$fn_name( $( $param_name.clone() ),* )
					,)*
					$call_type::__PhantomItem(_) => unreachable!(),
				}
			}
		}
		impl<$trait_instance: $trait_name> $crate::dispatch::PartialEq
			for $call_type<$trait_instance>
		{
			fn eq(&self, other: &Self) -> bool {
				match *self {
					$(
						$call_type::$fn_name( $( ref $param_name ),* ) => {
							let self_params = ( $( $param_name, )* );
							if let $call_type::$fn_name( $( ref $param_name ),* ) = *other {
								self_params == ( $( $param_name, )* )
							} else {
								if let $call_type::__PhantomItem(_) = *other {
									unreachable!()
								} else {
									false
								}
							}
						}
					)*
					$call_type::__PhantomItem(_) => unreachable!(),
				}
			}
		}
		impl<$trait_instance: $trait_name> $crate::dispatch::Eq
			for $call_type<$trait_instance>
		{}

		#[cfg(feature = "std")]
		impl<$trait_instance: $trait_name> $crate::dispatch::fmt::Debug
			for $call_type<$trait_instance>
		{
			fn fmt(&self, f: &mut $crate::dispatch::fmt::Formatter) -> $crate::dispatch::result::Result<(), $crate::dispatch::fmt::Error> {
				match *self {
					$(
						$call_type::$fn_name( $( ref $param_name ),* ) =>
							write!(f, "{}{:?}",
								stringify!($fn_name),
								( $( $param_name.clone(), )* )
							)
					,)*
					$call_type::__PhantomItem(_) => unreachable!(),
				}
			}
		}

		impl<$trait_instance: $trait_name> $crate::dispatch::Slicable for $call_type<$trait_instance> {
			fn decode<I: $crate::dispatch::Input>(input: &mut I) -> Option<Self> {
				match input.read_byte()? {
					$(
						$id => {
							$(
								let $param_name = $crate::dispatch::Slicable::decode(input)?;
							)*
							Some($call_type:: $fn_name( $( $param_name ),* ))
						}
					)*
					_ => None,
				}
			}

			fn encode(&self) -> $crate::dispatch::Vec<u8> {
				let mut v = $crate::dispatch::Vec::new();
				match *self {
					$(
						$call_type::$fn_name(
							$(
								ref $param_name
							),*
						) => {
							v.push($id as u8);
							$(
								$param_name.using_encoded(|s| v.extend(s));
							)*
						}
					)*
					$call_type::__PhantomItem(_) => unreachable!(),
				}
				v
			}

			fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
				f(self.encode().as_slice())
			}
		}

	}
}

pub trait IsSubType<T: Callable> {
	fn is_sub_type(&self) -> Option<&<T as Callable>::Call>;
}
pub trait IsAuxSubType<T: AuxCallable> {
	fn is_aux_sub_type(&self) -> Option<&<T as AuxCallable>::Call>;
}

/// Implement a meta-dispatch module to dispatch to other dispatchers.
#[macro_export]
macro_rules! impl_outer_dispatch {
	() => ();
	(
		$(#[$attr:meta])*
		pub enum $call_type:ident where aux: $aux:ty {
			$(
				$camelcase:ident = $id:expr,
			)*
		}
		$( $rest:tt )*
	) => {
		$(#[$attr])*
		pub enum $call_type {
			$(
				$camelcase ( $crate::dispatch::AuxCallableCallFor<$camelcase> )
			,)*
		}
		impl_outer_dispatch_common! { $call_type, $($camelcase = $id,)* }
		impl $crate::dispatch::AuxDispatchable for $call_type {
			type Aux = $aux;
			type Trait = $call_type;
			fn dispatch(self, aux: &$aux) -> $crate::dispatch::Result {
				match self {
					$(
						$call_type::$camelcase(call) => call.dispatch(&aux),
					)*
				}
			}
		}
		$(
			impl $crate::dispatch::IsAuxSubType<$camelcase> for $call_type {
				fn is_aux_sub_type(&self) -> Option<&<$camelcase as $crate::dispatch::AuxCallable>::Call> {
					if let $call_type::$camelcase ( ref r ) = *self {
						Some(r)
					} else {
						None
					}
				}
			}
		)*
		impl_outer_dispatch!{ $($rest)* }
	};
	(
		$(#[$attr:meta])*
		pub enum $call_type:ident {
			$(
				$camelcase:ident = $id:expr,
			)*
		}
		$( $rest:tt )*
	) => {
		$(#[$attr])*
		pub enum $call_type {
			$(
				$camelcase ( $crate::dispatch::CallableCallFor<$camelcase> )
			,)*
		}
		impl_outer_dispatch_common! { $call_type, $($camelcase = $id,)* }
		impl $crate::dispatch::Dispatchable for $call_type {
			type Trait = $call_type;
			fn dispatch(self) -> $crate::dispatch::Result {
				match self {
					$(
						$call_type::$camelcase(call) => call.dispatch(),
					)*
				}
			}
		}
		$(
			impl $crate::dispatch::IsSubType<$camelcase> for $call_type {
				fn is_sub_type(&self) -> Option<&<$camelcase as $crate::dispatch::Callable>::Call> {
					if let $call_type::$camelcase ( ref r ) = *self {
						Some(r)
					} else {
						None
					}
				}
			}
		)*
		impl_outer_dispatch!{ $($rest)* }
	}
}

/// Implement a meta-dispatch module to dispatch to other dispatchers.
#[macro_export]
macro_rules! impl_outer_dispatch_common {
	(
		$call_type:ident, $( $camelcase:ident = $id:expr, )*
	) => {
		impl $crate::dispatch::Slicable for $call_type {
			fn decode<I: $crate::dispatch::Input>(input: &mut I) -> Option<Self> {
				match input.read_byte()? {
					$(
						$id =>
							Some($call_type::$camelcase( $crate::dispatch::Slicable::decode(input)? )),
					)*
					_ => None,
				}
			}

			fn encode(&self) -> $crate::dispatch::Vec<u8> {
				let mut v = $crate::dispatch::Vec::new();
				match *self {
					$(
						$call_type::$camelcase( ref sub ) => {
							v.push($id as u8);
							sub.using_encoded(|s| v.extend(s));
						}
					)*
				}
				v
			}

			fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
				f(self.encode().as_slice())
			}
		}

	}
}
