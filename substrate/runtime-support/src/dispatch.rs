// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Dispatch system. Just dispatches calls.

pub use rstd::prelude::{Vec, Clone, Eq, PartialEq};
#[cfg(feature = "std")]
pub use std::fmt;
pub use rstd::result;
#[cfg(feature = "std")]
use serde;
pub use codec::{Codec, Decode, Encode, Input, Output};

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
	type Call: AuxDispatchable + Codec + ::serde::Serialize + Clone + PartialEq + Eq;
}
#[cfg(not(feature = "std"))]
pub trait AuxCallable {
	type Call: AuxDispatchable + Codec + Clone + PartialEq + Eq;
}

// dirty hack to work around serde_derive issue
// https://github.com/rust-lang/rust/issues/51331
pub type AuxCallableCallFor<A> = <A as AuxCallable>::Call;

#[cfg(feature = "std")]
pub trait Callable {
	type Call: Dispatchable + Codec + ::serde::Serialize + Clone + PartialEq + Eq;
}
#[cfg(not(feature = "std"))]
pub trait Callable {
	type Call: Dispatchable + Codec + Clone + PartialEq + Eq;
}

// dirty hack to work around serde_derive issue.
// https://github.com/rust-lang/rust/issues/51331
pub type CallableCallFor<C> = <C as Callable>::Call;

#[cfg(feature = "std")]
pub trait Parameter: Codec + serde::Serialize + Clone + Eq + fmt::Debug {}

#[cfg(feature = "std")]
impl<T> Parameter for T where T: Codec + serde::Serialize + Clone + Eq + fmt::Debug {}

#[cfg(not(feature = "std"))]
pub trait Parameter: Codec + Clone + Eq {}

#[cfg(not(feature = "std"))]
impl<T> Parameter for T where T: Codec + Clone + Eq {}

/// Declare a struct for this module, then implement dispatch logic to create a pairing of several
/// dispatch traits and enums.
#[macro_export]
macro_rules! decl_module {
	(
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>;
		$($rest:tt)*
	) => {
		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
		// TODO: switching based on std feature is because of an issue in
		// serde-derive for when we attempt to derive `Deserialize` on these types,
		// in a situation where we've imported `substrate_runtime_support` as another name.
		#[cfg(feature = "std")]
		$(#[$attr])*
		pub struct $mod_type<$trait_instance: $trait_name>(::std::marker::PhantomData<$trait_instance>);

		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
		#[cfg(not(feature = "std"))]
		$(#[$attr])*
		pub struct $mod_type<$trait_instance: $trait_name>(::core::marker::PhantomData<$trait_instance>);

		decl_dispatch! {
			impl for $mod_type<$trait_instance: $trait_name>;
			$($rest)*
		}

		__impl_json_metadata! {
			impl for $mod_type<$trait_instance: $trait_name>;
			$($rest)*
		}
	};
	(
		$(#[$attr:meta])*
		struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>;
		$($rest:tt)*
	) => {
		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
		#[cfg(feature = "std")]
		$(#[$attr])*
		struct $mod_type<$trait_instance: $trait_name>(::std::marker::PhantomData<$trait_instance>);

		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
		#[cfg(not(feature = "std"))]
		$(#[$attr])*
		struct $mod_type<$trait_instance: $trait_name>(::core::marker::PhantomData<$trait_instance>);
		decl_dispatch! {
			impl for $mod_type<$trait_instance: $trait_name>;
			$($rest)*
		}

		__impl_json_metadata! {
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
				$(#[$fn_attr:meta])*
				fn $fn_name:ident(
					$(
						$param_name:ident : $param:ty
					),*
				) -> $result:ty;
			)*
		}
		$($rest:tt)*
	) => {
		__decl_dispatch_module_without_aux! {
			impl for $mod_type<$trait_instance: $trait_name>;
			$(#[$attr])*
			pub enum $call_type;
			$(
				fn $fn_name( $( $param_name: $param ),* ) -> $result;
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
				$(#[$fn_attr:meta])*
				fn $fn_name:ident(aux
					$(
						, $param_name:ident : $param:ty
					)*
				) -> $result:ty;
			)*
		}
		$($rest:tt)*
	) => {
		__decl_dispatch_module_with_aux! {
			impl for $mod_type<$trait_instance: $trait_name>;
			$(#[$attr])*
			pub enum $call_type where aux: $aux_type;
			$(
				fn $fn_name(aux $(, $param_name: $param )*) -> $result;
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
#[doc(hidden)]
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
			-> $result:ty;
		)*
	) => {
		__decl_dispatch_module_common! {
			impl for $mod_type<$trait_instance: $trait_name>;
			$(#[$attr])*
			pub enum $call_type;
			$( fn $fn_name( $( $param_name : $param ),* ) -> $result; )*
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
#[doc(hidden)]
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
			-> $result:ty;
		)*
	) => {
		__decl_dispatch_module_common! {
			impl for $mod_type<$trait_instance: $trait_name>;
			$(#[$attr])*
			pub enum $call_type;
			$( fn $fn_name( $( $param_name : $param ),* ) -> $result; )*
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
#[doc(hidden)]
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
			-> $result:ty;
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

		impl<$trait_instance: $trait_name> $crate::dispatch::Decode for $call_type<$trait_instance> {
			fn decode<I: $crate::dispatch::Input>(input: &mut I) -> Option<Self> {
				let input_id = input.read_byte()?;
				__impl_decode!(input; input_id; 0; $call_type; $( fn $fn_name( $( $param_name ),* ); )*)
			}
		}

		impl<$trait_instance: $trait_name> $crate::dispatch::Encode for $call_type<$trait_instance> {
			fn encode_to<W: $crate::dispatch::Output>(&self, dest: &mut W) {
				__impl_encode!(dest; *self; 0; $call_type; $( fn $fn_name( $( $param_name ),* ); )*);
				if let $call_type::__PhantomItem(_) = *self { unreachable!() }
			}
		}
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __impl_decode {
	(
		$input:expr;
		$input_id:expr;
		$fn_id:expr;
		$call_type:ident;
		fn $fn_name:ident(
			$( $param_name:ident ),*
		);
		$($rest:tt)*
	) => {
		{
			if $input_id == ($fn_id) {
				$(
					let $param_name = $crate::dispatch::Decode::decode($input)?;
				)*
				return Some($call_type:: $fn_name( $( $param_name ),* ));
			}
							
			__impl_decode!($input; $input_id; $fn_id + 1; $call_type; $($rest)*)
		}
	};
	(
		$input:expr;
		$input_id:expr;
		$fn_id:expr;
		$call_type:ident;
	) => {
		None
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __impl_encode {
	(
		$dest:expr;
		$self:expr;
		$fn_id:expr;
		$call_type:ident;
		fn $fn_name:ident(
			$( $param_name:ident ),*
		);
		$($rest:tt)*
	) => {
		{
			if let $call_type::$fn_name(
				$(
					ref $param_name
				),*
			) = $self {
				$dest.push_byte(($fn_id) as u8);
				$(
					$param_name.encode_to($dest);
				)*
			}
							
			__impl_encode!($dest; $self; $fn_id + 1; $call_type; $($rest)*)
		}
	};
	(
		$dest:expr;
		$self:expr;
		$fn_id:expr;
		$call_type:ident;
	) => {{}}
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
				$camelcase:ident,
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
		__impl_outer_dispatch_common! { $call_type, $($camelcase,)* }
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
				$camelcase:ident,
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
		__impl_outer_dispatch_common! { $call_type, $($camelcase,)* }
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
#[doc(hidden)]
macro_rules! __impl_outer_dispatch_common {
	(
		$call_type:ident, $( $camelcase:ident, )*
	) => {
		impl $crate::dispatch::Decode for $call_type {
			fn decode<I: $crate::dispatch::Input>(input: &mut I) -> Option<Self> {
				let input_id = input.read_byte()?;
				__impl_decode!(input; input_id; 0; $call_type; $( fn $camelcase ( outer_dispatch_param ); )*)
			}
		}

		impl $crate::dispatch::Encode for $call_type {
			fn encode_to<W: $crate::dispatch::Output>(&self, dest: &mut W) {
				__impl_encode!(dest; *self; 0; $call_type; $( fn $camelcase( outer_dispatch_param ); )*)
			}
		}

	}
}

/// Implement the `json_metadata` function.
#[macro_export]
#[doc(hidden)]
macro_rules! __impl_json_metadata {
	(
		impl for $mod_type:ident<$trait_instance:ident: $trait_name:ident>;
		$($rest:tt)*
	) => {
		impl<$trait_instance: $trait_name> $mod_type<$trait_instance> {
			pub fn json_metadata() -> &'static str {
				concat!(r#"{ "name": ""#, stringify!($mod_type), r#"", "calls": ["#,
					__calls_to_json!(""; $($rest)*), " ] }")
			}
		}
	}
}

/// Convert the list of calls into their JSON representation, joined by ",".
#[macro_export]
#[doc(hidden)]
macro_rules! __calls_to_json {
	// WITHOUT AUX
	(
		$prefix_str:tt;
		$(#[$attr:meta])*
		pub enum $call_type:ident {
			$(
				$(#[doc = $doc_attr:tt])*
				fn $fn_name:ident(
					$(
						$param_name:ident : $param:ty
					),*
				) -> $result:ty;
			)*
		}
		$($rest:tt)*
	) => {
		concat!($prefix_str, " ",
			r#"{ "name": ""#, stringify!($call_type),
			r#"", "functions": {"#,
			__functions_to_json!(""; 0; $(
				fn $fn_name( $( $param_name: $param ),* ) -> $result;
				__function_doc_to_json!(""; $($doc_attr)*);
			)*), " } }", __calls_to_json!(","; $($rest)*)
		)
	};
	// WITH AUX
	(
		$prefix_str:tt;
		$(#[$attr:meta])*
		pub enum $call_type:ident where aux: $aux_type:ty {
			$(
				$(#[doc = $doc_attr:tt])*
				fn $fn_name:ident(aux
					$(
						, $param_name:ident : $param:ty
					)*
				) -> $result:ty;
			)*
		}
		$($rest:tt)*
	) => {
		concat!($prefix_str, " ",
			r#"{ "name": ""#, stringify!($call_type),
			r#"", "functions": {"#,
			__functions_to_json!(""; 0; $aux_type; $(
				fn $fn_name(aux $(, $param_name: $param )* ) -> $result;
				__function_doc_to_json!(""; $($doc_attr)*);
			)*), " } }", __calls_to_json!(","; $($rest)*)
		)
	};
	// BASE CASE
	(
		$prefix_str:tt;
	) => {
		""
	}
}

/// Convert a list of function into their JSON representation, joined by ",".
#[macro_export]
#[doc(hidden)]
macro_rules! __functions_to_json {
	// WITHOUT AUX
	(
		$prefix_str:tt;
		$fn_id:expr;
		fn $fn_name:ident(
			$($param_name:ident : $param:ty),*
		) -> $result:ty;
		$fn_doc:expr;
		$($rest:tt)*
	) => {
			concat!($prefix_str, " ",
				__function_to_json!(
					fn $fn_name(
						$($param_name : $param),*
					) -> $result;
					$fn_doc;
					$fn_id;
				), __functions_to_json!(","; $fn_id + 1; $($rest)*)
			)
	};
	// WITH AUX
	(
		$prefix_str:tt;
		$fn_id:expr;
		$aux_type:ty;
		fn $fn_name:ident(aux
			$(
				, $param_name:ident : $param:ty
			)*
		) -> $result:ty;
		$fn_doc:expr;
		$($rest:tt)*
	) => {
			concat!($prefix_str, " ",
				__function_to_json!(
					fn $fn_name(
						aux: $aux_type
						$(, $param_name : $param)*
					) -> $result;
					$fn_doc;
					$fn_id;
				), __functions_to_json!(","; $fn_id + 1; $aux_type; $($rest)*)
			)
	};
	// BASE CASE
	(
		$prefix_str:tt;
		$fn_id:expr;
		$($aux_type:ty;)*
	) => {
		""
	}
}

/// Convert a function into its JSON representation.
#[macro_export]
#[doc(hidden)]
macro_rules! __function_to_json {
	(
		fn $fn_name:ident(
			$first_param_name:ident : $first_param:ty $(, $param_name:ident : $param:ty)*
		) -> $result:ty;
		$fn_doc:tt;
		$fn_id:expr;
	) => {
			concat!(
				r#"""#, stringify!($fn_id), r#"""#,
				r#": { "name": ""#, stringify!($fn_name),
				r#"", "params": [ "#,
				concat!(r#"{ "name": ""#, stringify!($first_param_name), r#"", "type": ""#, stringify!($first_param), r#"" }"# ),
				$(
					concat!(r#", { "name": ""#, stringify!($param_name), r#"", "type": ""#, stringify!($param), r#"" }"# ),
				)*
				r#" ], "description": ["#, $fn_doc, " ] }"
			)
	};
}

/// Convert a function documentation attribute into its JSON representation.
#[macro_export]
#[doc(hidden)]
macro_rules! __function_doc_to_json {
	(
		$prefix_str:tt;
		$doc_attr:tt
		$($rest:tt)*
	) => {
			concat!(
				$prefix_str, r#" ""#,
				$doc_attr,
				r#"""#,
				__function_doc_to_json!(","; $($rest)*)
			)
	};
	(
		$prefix_str:tt;
	) => {
		""
	}
}

#[cfg(test)]
// Do not complain about unused `dispatch` and `dispatch_aux`.
#[allow(dead_code)]
mod tests {
	use super::*;
	use serde;
	use serde_json;

	pub trait Trait {
		 type PublicAux;
	}

	decl_module! {
		pub struct Module<T: Trait>;

		#[derive(Serialize, Deserialize)]
		pub enum Call where aux: T::PublicAux {
			/// Hi, this is a comment.
			fn aux_0(aux) -> Result;
			fn aux_1(aux, data: i32) -> Result;
			fn aux_2(aux, data: i32, data2: String) -> Result;
		}

		#[derive(Serialize, Deserialize)]
		pub enum PrivCall {
			/// Hi, this is a comment.
			/// Hi, this is a second comment.
			fn priv_0(data: String) -> Result;
			fn priv_1(data: String, data2: u32) -> Result;
		}
	}

	const EXPECTED_METADATA: &str = concat!(
		r#"{ "name": "Module", "calls": [ "#,
			r#"{ "name": "Call", "functions": { "#,
				r#""0": { "name": "aux_0", "params": [ "#,
					r#"{ "name": "aux", "type": "T::PublicAux" }"#,
				r#" ], "description": [ " Hi, this is a comment." ] }, "#,
				r#""0 + 1": { "name": "aux_1", "params": [ "#,
					r#"{ "name": "aux", "type": "T::PublicAux" }, "#,
					r#"{ "name": "data", "type": "i32" }"#,
				r#" ], "description": [ ] }, "#,
				r#""0 + 1 + 1": { "name": "aux_2", "params": [ "#,
					r#"{ "name": "aux", "type": "T::PublicAux" }, "#,
					r#"{ "name": "data", "type": "i32" }, "#,
					r#"{ "name": "data2", "type": "String" }"#,
				r#" ], "description": [ ] }"#,
			r#" } }, "#,
			r#"{ "name": "PrivCall", "functions": { "#,
				r#""0": { "name": "priv_0", "params": [ "#,
					r#"{ "name": "data", "type": "String" }"#,
				r#" ], "description": [ " Hi, this is a comment.", " Hi, this is a second comment." ] }, "#,
				r#""0 + 1": { "name": "priv_1", "params": [ "#,
					r#"{ "name": "data", "type": "String" }, "#,
					r#"{ "name": "data2", "type": "u32" }"#,
				r#" ], "description": [ ] }"#,
			r#" } }"#,
		r#" ] }"#,
	);

	impl<T: Trait> Module<T> {
		fn aux_0(_: &T::PublicAux) -> Result {
			unreachable!()
		}

		fn aux_1(_: &T::PublicAux, _: i32) -> Result {
			unreachable!()
		}

		fn aux_2(_: &T::PublicAux, _: i32, _: String) -> Result {
			unreachable!()
		}

		fn priv_0(_: String) -> Result {
			unreachable!()
		}

		fn priv_1(_: String, _: u32) -> Result {
			unreachable!()
		}
	}

	struct TraitImpl {}

	impl Trait for TraitImpl {
		type PublicAux = u32;
	}

	#[test]
	fn module_json_metadata() {
		let metadata = Module::<TraitImpl>::json_metadata();
		assert_eq!(EXPECTED_METADATA, metadata);
		let _: serde::de::IgnoredAny =
			serde_json::from_str(metadata).expect("Is valid json syntax");
	}
}