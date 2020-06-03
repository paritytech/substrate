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

// You should have received a copy of the GNU General Public License
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

//! Definition of macros that hides boilerplate of defining external environment
//! for a wasm module.
//!
//! Most likely you should use `define_env` macro.

#[macro_export]
macro_rules! convert_args {
	() => (vec![]);
	( $( $t:ty ),* ) => ( vec![ $( { use $crate::exec::env_def::ConvertibleToWasm; <$t>::VALUE_TYPE }, )* ] );
}

#[macro_export]
macro_rules! gen_signature {
	( ( $( $params: ty ),* ) ) => (
		{
			parity_wasm::elements::FunctionType::new(convert_args!($($params),*), None)
		}
	);

	( ( $( $params: ty ),* ) -> $returns: ty ) => (
		{
			parity_wasm::elements::FunctionType::new(convert_args!($($params),*), Some({
				use $crate::exec::env_def::ConvertibleToWasm; <$returns>::VALUE_TYPE
			}))
		}
	);
}

#[macro_export]
macro_rules! gen_signature_dispatch {
	(
		$needle_name:ident,
		$needle_sig:ident ;
		$name:ident
		( $ctx:ident $( , $names:ident : $params:ty )* ) $( -> $returns:ty )* , $($rest:tt)* ) => {
		if stringify!($name).as_bytes() == $needle_name {
			let signature = gen_signature!( ( $( $params ),* ) $( -> $returns )* );
			if $needle_sig == &signature {
				return true;
			}
		} else {
			gen_signature_dispatch!($needle_name, $needle_sig ; $($rest)*);
		}
	};
	( $needle_name:ident, $needle_sig:ident ; ) => {
	};
}

/// Unmarshall arguments and then execute `body` expression and return its result.
macro_rules! unmarshall_then_body {
	( $body:tt, $ctx:ident, $args_iter:ident, $( $names:ident : $params:ty ),* ) => ({
		$(
			let $names : <$params as $crate::exec::env_def::ConvertibleToWasm>::NativeType =
				$args_iter.next()
					.and_then(|v| <$params as $crate::exec::env_def::ConvertibleToWasm>
						::from_typed_value(v.clone()))
					.expect(
						"precondition: all imports should be checked against the signatures of corresponding
						functions defined by `define_env!` macro by the user of the macro;
						signatures of these functions defined by `$params`;
						calls always made with arguments types of which are defined by the corresponding imports;
						thus types of arguments should be equal to type list in `$params` and
						length of argument list and $params should be equal;
						thus this can never be `None`;
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
	F: FnOnce() -> Result<R, sp_sandbox::HostError>,
{
	f
}

#[macro_export]
macro_rules! unmarshall_then_body_then_marshall {
	( $args_iter:ident, $ctx:ident, ( $( $names:ident : $params:ty ),* ) -> $returns:ty => $body:tt ) => ({
		let body = $crate::exec::env_def::macros::constrain_closure::<
			<$returns as $crate::exec::env_def::ConvertibleToWasm>::NativeType, _
		>(|| {
			unmarshall_then_body!($body, $ctx, $args_iter, $( $names : $params ),*)
		});
		let r = body()?;
		return Ok(sp_sandbox::ReturnValue::Value({ use $crate::exec::env_def::ConvertibleToWasm; r.to_typed_value() }))
	});
	( $args_iter:ident, $ctx:ident, ( $( $names:ident : $params:ty ),* ) => $body:tt ) => ({
		let body = $crate::exec::env_def::macros::constrain_closure::<(), _>(|| {
			unmarshall_then_body!($body, $ctx, $args_iter, $( $names : $params ),*)
		});
		body()?;
		return Ok(sp_sandbox::ReturnValue::Unit)
	})
}

#[macro_export]
macro_rules! define_func {
	( < E: $ext_ty:tt > $name:ident ( $ctx:ident : $ctx_ty:ty $(, $names:ident : $params:ty)*) $(-> $returns:ty)* => $body:tt ) => {
		fn $name< E: $ext_ty >(
			$ctx: $ctx_ty,
			args: &[sp_sandbox::Value],
		) -> Result<sp_sandbox::ReturnValue, sp_sandbox::HostError> {
			#[allow(unused)]
			let mut args = args.iter();

			unmarshall_then_body_then_marshall!(
				args,
				$ctx,
				( $( $names : $params ),* ) $( -> $returns )* => $body
			)
		}
	};
}

#[macro_export]
macro_rules! register_func {
	( $reg_cb:ident, < E: $ext_ty:tt > ; ) => {};

	( $reg_cb:ident, < E: $ext_ty:tt > ;
		$name:ident ( $ctx:ident : $ctx_ty:ty $( , $names:ident : $params:ty )* )
		$( -> $returns:ty )* => $body:tt $($rest:tt)*
	) => {
		$reg_cb(
			stringify!($name).as_bytes(),
			{
				define_func!(
					< E: $ext_ty > $name ( $ctx : $ctx_ty $(, $names : $params )* ) $( -> $returns )* => $body
				);
				$name::<E>
			}
		);
		register_func!( $reg_cb, < E: $ext_ty > ; $($rest)* );
	};
}

/// Define a function set that can be imported by executing wasm code.
///
/// **NB**: Be advised that all functions defined by this macro
/// will panic if called with unexpected arguments.
///
/// It's up to the user of this macro to check signatures of wasm code to be executed
/// and reject the code if any imported function has a mismatched signature.
macro_rules! define_env {
	( $init_name:ident , < E: $ext_ty:tt > ,
		$( $name:ident ( $ctx:ident : $ctx_ty:ty $( , $names:ident : $params:ty )* )
			$( -> $returns:ty )* => $body:tt , )*
	) => {
		pub struct $init_name;

		impl $crate::exec::env_def::ImportSatisfyCheck for $init_name {
			fn can_satisfy(name: &[u8], func_type: &parity_wasm::elements::FunctionType) -> bool {
				gen_signature_dispatch!( name, func_type ; $( $name ( $ctx $(, $names : $params )* ) $( -> $returns )* , )* );

				return false;
			}
		}

		impl<E: Ext> $crate::exec::env_def::FunctionImplProvider<E> for $init_name {
			fn impls<F: FnMut(&[u8], $crate::exec::env_def::HostFunc<E>)>(f: &mut F) {
				register_func!(f, < E: $ext_ty > ; $( $name ( $ctx : $ctx_ty $( , $names : $params )* ) $( -> $returns)* => $body )* );
			}
		}
	};
}
