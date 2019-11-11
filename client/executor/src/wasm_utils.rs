// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Utilities for defining the wasm host environment.

use wasm_interface::{Pointer, WordSize};

/// Converts arguments into respective WASM types.
#[macro_export]
macro_rules! convert_args {
	() => ([]);
	( $( $t:ty ),* ) => ( [ $( <$t as $crate::wasm_interface::IntoValue>::VALUE_TYPE, )* ] );
}

/// Generates a WASM signature for given list of parameters.
#[macro_export]
macro_rules! gen_signature {
	( ( $( $params: ty ),* ) ) => (
		$crate::wasm_interface::Signature {
			args: std::borrow::Cow::Borrowed(&convert_args!( $( $params ),* )[..]),
			return_value: None,
		}
	);
	( ( $( $params: ty ),* ) -> $returns:ty ) => (
		$crate::wasm_interface::Signature {
			args: std::borrow::Cow::Borrowed(&convert_args!( $( $params ),* )[..]),
			return_value: Some(<$returns as $crate::wasm_interface::IntoValue>::VALUE_TYPE),
		}
	);
}

macro_rules! gen_functions {
	(@INTERNAL
		{ $( $generated:tt )* }
		$context:ident,
	) => (
		vec![ $( $generated )* ]
	);
	(@INTERNAL
		{ $( $generated:tt )* }
		$context:ident,
		$name:ident ( $( $names:ident: $params:ty ),* ) $( -> $returns:ty )? { $( $body:tt )* }
		$( $tail:tt )*
	) => (
		gen_functions! {
			@INTERNAL
			{
				$( $generated )*
				{
					struct $name;

					#[allow(unused)]
					impl $crate::wasm_interface::Function for $name {
						fn name(&self) -> &str {
							stringify!($name)
						}
						fn signature(&self) -> $crate::wasm_interface::Signature {
							gen_signature!( ( $( $params ),* ) $( -> $returns )? )
						}
						fn execute(
							&self,
							context: &mut dyn $crate::wasm_interface::FunctionContext,
							args: &mut dyn Iterator<Item=$crate::wasm_interface::Value>,
						) -> ::std::result::Result<Option<$crate::wasm_interface::Value>, String> {
							let mut $context = context;
							marshall! {
								args,
								( $( $names : $params ),* ) $( -> $returns )? => { $( $body )* }
							}
						}
					}

					&$name as &dyn $crate::wasm_interface::Function
				},
			}
			$context,
			$( $tail )*
		}
	);

	( $context:ident, $( $tail:tt )* ) => (
		gen_functions!(@INTERNAL {} $context, $($tail)*);
	);
}

/// Converts the list of arguments coming from WASM into their native types.
#[macro_export]
macro_rules! unmarshall_args {
	( $body:tt, $args_iter:ident, $( $names:ident : $params:ty ),*) => ({
		$(
			let $names : $params =
				$args_iter.next()
					.and_then(|val| <$params as $crate::wasm_interface::TryFromValue>::try_from_value(val))
					.expect(
						"`$args_iter` comes from an argument of Externals::execute_function;
						args to an external call always matches the signature of the external;
						external signatures are built with count and types and in order defined by `$params`;
						here, we iterating on `$params`;
						qed;
						"
					);
		)*
		$body
	})
}

/// Since we can't specify the type of closure directly at binding site:
///
/// ```nocompile
/// let f: FnOnce() -> Result<<u32 as ConvertibleToWasm>::NativeType, _> = || { /* ... */ };
/// ```
///
/// we use this function to constrain the type of the closure.
#[inline(always)]
pub fn constrain_closure<R, F>(f: F) -> F
where
	F: FnOnce() -> Result<R, String>
{
	f
}

/// Pass the list of parameters by converting them to respective WASM types.
#[macro_export]
macro_rules! marshall {
	( $args_iter:ident, ( $( $names:ident : $params:ty ),* ) -> $returns:ty => $body:tt ) => ({
		let body = $crate::wasm_utils::constrain_closure::<$returns, _>(|| {
			unmarshall_args!($body, $args_iter, $( $names : $params ),*)
		});
		let r = body()?;
		return Ok(Some($crate::wasm_interface::IntoValue::into_value(r)))
	});
	( $args_iter:ident, ( $( $names:ident : $params:ty ),* ) => $body:tt ) => ({
		let body = $crate::wasm_utils::constrain_closure::<(), _>(|| {
			unmarshall_args!($body, $args_iter, $( $names : $params ),*)
		});
		body()?;
		return Ok(None)
	})
}

/// Implements the wasm host interface for the given type.
#[macro_export]
macro_rules! impl_wasm_host_interface {
	(
		impl $interface_name:ident where $context:ident {
			$(
				$name:ident($( $names:ident : $params:ty ),* $(,)? ) $( -> $returns:ty )?
				{ $( $body:tt )* }
			)*
		}
	) => (
		impl $crate::wasm_interface::HostFunctions for $interface_name {
			#[allow(non_camel_case_types)]
			fn host_functions() -> Vec<&'static dyn $crate::wasm_interface::Function> {
				gen_functions!(
					$context,
					$( $name( $( $names: $params ),* ) $( -> $returns )? { $( $body )* } )*
				)
			}
		}
	);
}

/// Runtime API functions return an i64 which encodes a pointer in the least-significant 32 bits
/// and a length in the most-significant 32 bits. This interprets the returned value as a pointer,
/// length tuple.
pub fn interpret_runtime_api_result(retval: i64) -> (Pointer<u8>, WordSize) {
	let ptr = <Pointer<u8>>::new(retval as u32);
	// The first cast to u64 is necessary so that the right shift does not sign-extend.
	let len = ((retval as u64) >> 32) as WordSize;
	(ptr, len)
}

