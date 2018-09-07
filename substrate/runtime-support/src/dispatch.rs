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
	type Origin;
	type Trait;
	fn dispatch(self, origin: Self::Origin) -> Result;
}

#[cfg(feature = "std")]
pub trait Callable {
	type Call: Dispatchable + Codec + ::serde::Serialize + Clone + PartialEq + Eq;
}
#[cfg(not(feature = "std"))]
pub trait Callable {
	type Call: Dispatchable + Codec + Clone + PartialEq + Eq;
}

// dirty hack to work around serde_derive issue
// https://github.com/rust-lang/rust/issues/51331
pub type CallableCallFor<A> = <A as Callable>::Call;

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
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty {$(
			$(#[doc = $doc_attr:tt])*
			fn $fn_name:ident(origin
				$(
					, $param_name:ident : $param:ty
				)*
			) -> $result:ty;
		)*}
	) => {
		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
		// TODO: switching based on std feature is because of an issue in
		// serde-derive for when we attempt to derive `Deserialize` on these types,
		// in a situation where we've imported `substrate_runtime_support` as another name.
		#[cfg(feature = "std")]
		pub struct $mod_type<$trait_instance: $trait_name>(::std::marker::PhantomData<$trait_instance>);

		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
		#[cfg(not(feature = "std"))]
		pub struct $mod_type<$trait_instance: $trait_name>(::core::marker::PhantomData<$trait_instance>);

		#[cfg(feature = "std")]
		$(#[$attr])*
		#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
		pub enum $call_type<$trait_instance: $trait_name> {
			__PhantomItem(::std::marker::PhantomData<$trait_instance>),
			__OtherPhantomItem(::std::marker::PhantomData<$trait_instance>),
			$(
				#[allow(non_camel_case_types)]
				$fn_name ( $( $param ),* ),
			)*
		}

		#[cfg(not(feature = "std"))]
		$(#[$attr])*
		#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
		pub enum $call_type<$trait_instance: $trait_name> {
			__PhantomItem(::core::marker::PhantomData<$trait_instance>),
			__OtherPhantomItem(::core::marker::PhantomData<$trait_instance>),
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
					_ => unreachable!(),
				}
			}
		}
		impl<$trait_instance: $trait_name> $crate::dispatch::PartialEq
			for $call_type<$trait_instance>
		{
			fn eq(&self, _other: &Self) -> bool {
				match *self {
					$(
						$call_type::$fn_name( $( ref $param_name ),* ) => {
							let self_params = ( $( $param_name, )* );
							if let $call_type::$fn_name( $( ref $param_name ),* ) = *_other {
								self_params == ( $( $param_name, )* )
							} else {
								match *_other {
									$call_type::__PhantomItem(_) => unreachable!(),
									$call_type::__OtherPhantomItem(_) => unreachable!(),
									_ => false,
								}
							}
						}
					)*
					_ => unreachable!(),
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
			fn fmt(&self, _f: &mut $crate::dispatch::fmt::Formatter) -> $crate::dispatch::result::Result<(), $crate::dispatch::fmt::Error> {
				match *self {
					$(
						$call_type::$fn_name( $( ref $param_name ),* ) =>
							write!(_f, "{}{:?}",
								stringify!($fn_name),
								( $( $param_name.clone(), )* )
							)
					,)*
					_ => unreachable!(),
				}
			}
		}

		impl<$trait_instance: $trait_name> $crate::dispatch::Decode for $call_type<$trait_instance> {
			fn decode<I: $crate::dispatch::Input>(input: &mut I) -> Option<Self> {
				let _input_id = input.read_byte()?;
				__impl_decode!(input; _input_id; 0; $call_type; $( fn $fn_name( $( $param_name ),* ); )*)
			}
		}

		impl<$trait_instance: $trait_name> $crate::dispatch::Encode for $call_type<$trait_instance> {
			fn encode_to<W: $crate::dispatch::Output>(&self, _dest: &mut W) {
				__impl_encode!(_dest; *self; 0; $call_type; $( fn $fn_name( $( $param_name ),* ); )*);
				if let $call_type::__PhantomItem(_) = *self { unreachable!() }
				if let $call_type::__OtherPhantomItem(_) = *self { unreachable!() }
			}
		}
		impl<$trait_instance: $trait_name> $crate::dispatch::Dispatchable
			for $call_type<$trait_instance>
		{
			type Trait = $trait_instance;
			type Origin = $origin_type;
			fn dispatch(self, _origin: Self::Origin) -> $crate::dispatch::Result {
				match self {
					$(
						$call_type::$fn_name( $( $param_name ),* ) =>
							<$mod_type<$trait_instance>>::$fn_name( _origin $(, $param_name )* ),
					)*
					_ => { panic!("__PhantomItem should never be used.") },
				}
			}
		}
		impl<$trait_instance: $trait_name> $crate::dispatch::Callable
			for $mod_type<$trait_instance>
		{
			type Call = $call_type<$trait_instance>;
		}

		impl<$trait_instance: $trait_name> $mod_type<$trait_instance> {
			pub fn dispatch<D: $crate::dispatch::Dispatchable<Trait = $trait_instance>>(d: D, origin: D::Origin) -> $crate::dispatch::Result {
				d.dispatch(origin)
			}
		}

		__impl_json_metadata! {
			$mod_type $trait_instance $trait_name $call_type $origin_type
			{$( $(#[doc = $doc_attr])* fn $fn_name(origin $(, $param_name : $param )*) -> $result; )*}
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
	fn is_aux_sub_type(&self) -> Option<&<T as Callable>::Call>;
}

/// Implement a meta-dispatch module to dispatch to other dispatchers.
#[macro_export]
macro_rules! impl_outer_dispatch {
	() => ();
	(
		$(#[$attr:meta])*
		pub enum $call_type:ident where origin: $origin:ty {
			$(
				$camelcase:ident,
			)*
		}
		$( $rest:tt )*
	) => {
		$(#[$attr])*
		#[derive(Clone, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
		pub enum $call_type {
			$(
				$camelcase ( $crate::dispatch::CallableCallFor<$camelcase> )
			,)*
		}
		__impl_outer_dispatch_common! { $call_type, $($camelcase,)* }
		impl $crate::dispatch::Dispatchable for $call_type {
			type Origin = $origin;
			type Trait = $call_type;
			fn dispatch(self, origin: $origin) -> $crate::dispatch::Result {
				match self {
					$(
						$call_type::$camelcase(call) => call.dispatch(origin),
					)*
				}
			}
		}
		$(
			impl $crate::dispatch::IsSubType<$camelcase> for $call_type {
				fn is_aux_sub_type(&self) -> Option<&<$camelcase as $crate::dispatch::Callable>::Call> {
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
		$mod_type:ident $trait_instance:ident $trait_name:ident
		$($rest:tt)*
	) => {
		impl<$trait_instance: $trait_name> $mod_type<$trait_instance> {
			pub fn json_metadata() -> &'static str {
				concat!(r#"{ "name": ""#, stringify!($mod_type), r#"", "call": [ "#,
					__call_to_json!($($rest)*), " ] }")
			}
		}
	}
}

/// Convert the list of calls into their JSON representation, joined by ",".
#[macro_export]
#[doc(hidden)]
macro_rules! __call_to_json {
	// WITH AUX
	(
		$call_type:ident $origin_type:ty
			{$(
				$(#[doc = $doc_attr:tt])*
				fn $fn_name:ident(origin
					$(
						, $param_name:ident : $param:ty
					)*
				) -> $result:ty;
			)*}
	) => {
		concat!(
			r#"{ "name": ""#, stringify!($call_type),
			r#"", "functions": {"#,
			__functions_to_json!(""; 0; $origin_type; $(
				fn $fn_name(origin $(, $param_name: $param )* ) -> $result;
				__function_doc_to_json!(""; $($doc_attr)*);
			)*), " } }"
		)
	};
}

/// Convert a list of functions into their JSON representation, joined by ",".
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
		$origin_type:ty;
		fn $fn_name:ident(origin
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
						origin: $origin_type
						$(, $param_name : $param)*
					) -> $result;
					$fn_doc;
					$fn_id;
				), __functions_to_json!(","; $fn_id + 1; $origin_type; $($rest)*)
			)
	};
	// BASE CASE
	(
		$prefix_str:tt;
		$fn_id:expr;
		$($origin_type:ty;)*
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
		type Origin;
	}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {
			/// Hi, this is a comment.
			fn aux_0(origin) -> Result;
			fn aux_1(origin, data: i32) -> Result;
			fn aux_2(origin, data: i32, data2: String) -> Result;
		}
	}

	const EXPECTED_METADATA: &str = concat!(
		r#"{ "name": "Module", "call": [ "#,
			r#"{ "name": "Call", "functions": { "#,
				r#""0": { "name": "aux_0", "params": [ "#,
					r#"{ "name": "origin", "type": "T::Origin" }"#,
				r#" ], "description": [ " Hi, this is a comment." ] }, "#,
				r#""0 + 1": { "name": "aux_1", "params": [ "#,
					r#"{ "name": "origin", "type": "T::Origin" }, "#,
					r#"{ "name": "data", "type": "i32" }"#,
				r#" ], "description": [ ] }, "#,
				r#""0 + 1 + 1": { "name": "aux_2", "params": [ "#,
					r#"{ "name": "origin", "type": "T::Origin" }, "#,
					r#"{ "name": "data", "type": "i32" }, "#,
					r#"{ "name": "data2", "type": "String" }"#,
				r#" ], "description": [ ] }"#,
			r#" } }"#,
		r#" ] }"#,
	);

	impl<T: Trait> Module<T> {
		fn aux_0(_: T::Origin) -> Result {
			unreachable!()
		}

		fn aux_1(_: T::Origin, _: i32) -> Result {
			unreachable!()
		}

		fn aux_2(_: T::Origin, _: i32, _: String) -> Result {
			unreachable!()
		}
	}

	struct TraitImpl {}

	impl Trait for TraitImpl {
		type Origin = u32;
	}

	#[test]
	fn module_json_metadata() {
		let metadata = Module::<TraitImpl>::json_metadata();
		assert_eq!(EXPECTED_METADATA, metadata);
		let _: serde::de::IgnoredAny =
			serde_json::from_str(metadata).expect("Is valid json syntax");
	}
}