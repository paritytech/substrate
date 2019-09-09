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

//! Rust implementation of Substrate contracts.

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
		{
			$crate::wasm_interface::Signature::new_with_args(&convert_args!( $( $params ),* )[..])
		}
	);
	( ( $( $params: ty ),* ) -> $returns: ty ) => (
		{
			$crate::wasm_interface::Signature::new(&convert_args!( $( $params ),*) [..], Some({
				<$returns as $crate::wasm_interface::IntoValue>::VALUE_TYPE
			}))
		}
	);
}

macro_rules! resolve_fn {
	(@iter $index:expr, $sig_var:ident, $name_var:ident) => ();
	(@iter
		$index:expr,
		$sig_var:ident,
		$name_var:ident
		$name:ident ( $( $params:ty ),* ) $( -> $returns:ty )?;
		$( $tail:tt )*
	) => (
		if $name_var == stringify!($name) {
			let fn_signature = gen_signature!( ( $( $params ),* ) $( -> $returns )? );
			if $sig_var != &fn_signature {
				return Err(format!("Export {} has different signature {:?}", $name_var, $sig_var));
			}
			return Ok(Some($crate::wasm_interface::FunctionRef::new(fn_signature, $index)));
		}
		resolve_fn!(@iter $index + 1, $sig_var, $name_var $( $tail )*)
	);

	($sig_var:ident, $name_var:ident, $($tail:tt)* ) => (
		resolve_fn!(@iter 0, $sig_var, $name_var $($tail)*);
	);
}

/// Converts the list of arguments coming from WASM into their native types.
#[macro_export]
macro_rules! unmarshall_args {
	( $body:tt, $objectname:ident, $args_iter:ident, $( $names:ident : $params:ty ),*) => ({
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
	( $args_iter:ident, $objectname:ident, ( $( $names:ident : $params:ty ),* ) -> $returns:ty => $body:tt ) => ({
		let body = $crate::wasm_utils::constrain_closure::<$returns, _>(|| {
			unmarshall_args!($body, $objectname, $args_iter, $( $names : $params ),*)
		});
		let r = body()?;
		return Ok(Some($crate::wasm_interface::IntoValue::into_value(r)))
	});
	( $args_iter:ident, $objectname:ident, ( $( $names:ident : $params:ty ),* ) => $body:tt ) => ({
		let body = $crate::wasm_utils::constrain_closure::<(), _>(|| {
			unmarshall_args!($body, $objectname, $args_iter, $( $names : $params ),*)
		});
		body()?;
		return Ok(None)
	})
}

macro_rules! dispatch_fn {
	( @iter $index:expr, $index_ident:ident, $objectname:ident, $args_iter:ident) => {
		// `$index` comes from an argument of Externals::invoke_index;
		// externals are always invoked with index given by resolve_fn! at resolve time;
		// For each next function resolve_fn! gives new index, starting from 0;
		// Both dispatch_fn! and resolve_fn! are called with the same list of functions;
		// qed;
		panic!("fn with index {} is undefined", $index);
	};

	(@iter
		$index:expr,
		$index_ident:ident,
		$objectname:ident,
		$args_iter:ident,
		$name:ident ( $( $names:ident : $params:ty ),* ) $( -> $returns:ty )* => $body:tt $($tail:tt)*
	) => (
		if $index_ident == $index {
			marshall!($args_iter, $objectname, ( $( $names : $params ),* ) $( -> $returns )* => $body)
		}
		dispatch_fn!( @iter $index + 1, $index_ident, $objectname, $args_iter $($tail)*)
	);

	( $index_ident:ident, $objectname:ident, $args_iter:ident, $($tail:tt)* ) => (
		dispatch_fn!( @iter 0, $index_ident, $objectname, $args_iter, $($tail)*);
	);
}

macro_rules! count_fns {
	(@iter $index:expr,) => {
		$index
	};
	(@iter $index:expr, $name:ident $( $tail:tt )* ) => (
		count_fns!(@iter $index + 1, $( $tail )*)
	);
	( $( $tail:tt )* ) => (
		count_fns!(@iter 0, $( $tail )*);
	);
}

/// Implements the wasm host interface for the given type.
#[macro_export]
macro_rules! impl_wasm_host_interface {
	(
		#[inherent_externals]
		impl $( < $( $gen:tt $(: $bound:path )? ),* > )? $interface_name:ident $( < $( $ty_gen:tt ),* > )?
			where $this:ident
		{
			$(
				$name:ident($( $names:ident : $params:ty ),* $(,)? ) $( -> $returns:ty )?
				{ $( $body:tt )* }
			)*
		}
	) => (
		impl $(< $( $gen $(: $bound )? ),* >)? $crate::wasm_interface::InherentHostFunctions
			for $interface_name $( < $( $ty_gen ),* > )?
		{
			fn resolve_function(
				name: &str,
				signature: &$crate::wasm_interface::Signature,
			) -> std::result::Result<Option<$crate::wasm_interface::FunctionRef>, String> {
				resolve_fn!(
					signature,
					name,
					$( $name( $( $params ),* ) $( -> $returns )?; )*
				);

				Ok(None)
			}
			fn function_count() -> usize {
				count_fns!( $( $name )* )
			}
			fn execute_function<A: Iterator<Item=$crate::wasm_interface::Value>>(
				&mut self,
				index: usize,
				mut args: A,
			) -> std::result::Result<Option<$crate::wasm_interface::Value>, String> {
				let $this = self;
				dispatch_fn! {
					index,
					$interface_name,
					args,
					$( $name( $( $names : $params ),* ) $( -> $returns )? => { $( $body )* } ),*
				};
			}
		}
	);
	(
		impl $( < $( $gen:tt $(: $bound:path )? ),* > )? $interface_name:ident $( < $( $ty_gen:tt ),* > )?
			where $context:ident
		{
			$(
				$name:ident($( $names:ident : $params:ty ),* $(,)? ) $( -> $returns:ty )?
				{ $( $body:tt )* }
			)*
		}
	) => (
		impl $(< $( $gen $(: $bound )? ),* >)? $crate::wasm_interface::HostFunctions
			for $interface_name $( < $( $ty_gen ),* > )?
		{
			fn resolve_function(
				name: &str,
				signature: &$crate::wasm_interface::Signature,
			) -> std::result::Result<Option<$crate::wasm_interface::FunctionRef>, String> {
				resolve_fn!(
					signature,
					name,
					$( $name( $( $params ),* ) $( -> $returns )?; )*
				);

				Ok(None)
			}
			fn function_count() -> usize {
				count_fns!( $( $name )* )
			}
			fn execute_function<A: Iterator<Item=$crate::wasm_interface::Value>>(
				index: usize,
				mut args: A,
				context: &mut dyn $crate::wasm_interface::HostFunctionsContext,
			) -> std::result::Result<Option<$crate::wasm_interface::Value>, String> {
				let mut $context = context;
				dispatch_fn! {
					index,
					$interface_name,
					args,
					$( $name( $( $names : $params ),* ) $( -> $returns )? => { $( $body )* } ),*
				};
			}
		}
	);
}
