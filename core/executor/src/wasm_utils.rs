// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
//! Rust implementation of Substrate contracts.

use wasmi::{ValueType, RuntimeValue, HostError};
use wasmi::nan_preserving_float::{F32, F64};
use std::fmt;

#[derive(Debug, PartialEq)]
pub struct UserError(pub &'static str);
impl fmt::Display for UserError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "UserError: {}", self.0)
	}
}
impl HostError for UserError {
}

pub trait ConvertibleToWasm { const VALUE_TYPE: ValueType; type NativeType; fn to_runtime_value(self) -> RuntimeValue; }
impl ConvertibleToWasm for i32 { type NativeType = i32; const VALUE_TYPE: ValueType = ValueType::I32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I32(self) } }
impl ConvertibleToWasm for u32 { type NativeType = u32; const VALUE_TYPE: ValueType = ValueType::I32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I32(self as i32) } }
impl ConvertibleToWasm for i64 { type NativeType = i64; const VALUE_TYPE: ValueType = ValueType::I64; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I64(self) } }
impl ConvertibleToWasm for u64 { type NativeType = u64; const VALUE_TYPE: ValueType = ValueType::I64; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I64(self as i64) } }
impl ConvertibleToWasm for F32 { type NativeType = F32; const VALUE_TYPE: ValueType = ValueType::F32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::F32(self) } }
impl ConvertibleToWasm for F64 { type NativeType = F64; const VALUE_TYPE: ValueType = ValueType::F64; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::F64(self) } }
impl ConvertibleToWasm for isize { type NativeType = i32; const VALUE_TYPE: ValueType = ValueType::I32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I32(self as i32) } }
impl ConvertibleToWasm for usize { type NativeType = u32; const VALUE_TYPE: ValueType = ValueType::I32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I32(self as u32 as i32) } }
impl<T> ConvertibleToWasm for *const T { type NativeType = u32; const VALUE_TYPE: ValueType = ValueType::I32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I32(self as isize as i32) } }
impl<T> ConvertibleToWasm for *mut T { type NativeType = u32; const VALUE_TYPE: ValueType = ValueType::I32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I32(self as isize as i32) } }

#[macro_export]
macro_rules! convert_args {
	() => ([]);
	( $( $t:ty ),* ) => ( [ $( { use $crate::wasm_utils::ConvertibleToWasm; <$t>::VALUE_TYPE }, )* ] );
}

#[macro_export]
macro_rules! gen_signature {
	( ( $( $params: ty ),* ) ) => (
		{
			$crate::wasmi::Signature::new(&convert_args!($($params),*)[..], None)
		}
	);

	( ( $( $params: ty ),* ) -> $returns: ty ) => (
		{
			$crate::wasmi::Signature::new(&convert_args!($($params),*)[..], Some({
				use $crate::wasm_utils::ConvertibleToWasm; <$returns>::VALUE_TYPE
			}))
		}
	);
}

macro_rules! resolve_fn {
	(@iter $index:expr, $sig_var:ident, $name_var:ident) => ();
	(@iter $index:expr, $sig_var:ident, $name_var:ident $name:ident ( $( $params:ty ),* ) $( -> $returns:ty )* => $($tail:tt)* ) => (
		if $name_var == stringify!($name) {
			let signature = gen_signature!( ( $( $params ),* ) $( -> $returns )* );
			if $sig_var != &signature {
				return Err($crate::wasmi::Error::Instantiation(
					format!("Export {} has different signature {:?}", $name_var, $sig_var),
				));
			}
			return Ok($crate::wasmi::FuncInstance::alloc_host(signature, $index));
		}
		resolve_fn!(@iter $index + 1, $sig_var, $name_var $($tail)*)
	);

	($sig_var:ident, $name_var:ident, $($tail:tt)* ) => (
		resolve_fn!(@iter 0, $sig_var, $name_var $($tail)*);
	);
}

#[macro_export]
macro_rules! unmarshall_args {
	( $body:tt, $objectname:ident, $args_iter:ident, $( $names:ident : $params:ty ),*) => ({
		$(
			let $names : <$params as $crate::wasm_utils::ConvertibleToWasm>::NativeType =
				$args_iter.next()
					.and_then(|rt_val| rt_val.try_into())
					.expect(
						"`$args_iter` comes from an argument of Externals::invoke_index;
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
	F: FnOnce() -> Result<R, ::wasmi::Trap>
{
	f
}

#[macro_export]
macro_rules! marshall {
	( $args_iter:ident, $objectname:ident, ( $( $names:ident : $params:ty ),* ) -> $returns:ty => $body:tt ) => ({
		let body = $crate::wasm_utils::constrain_closure::<
			<$returns as $crate::wasm_utils::ConvertibleToWasm>::NativeType, _
		>(|| {
			unmarshall_args!($body, $objectname, $args_iter, $( $names : $params ),*)
		});
		let r = body()?;
		return Ok(Some({ use $crate::wasm_utils::ConvertibleToWasm; r.to_runtime_value() }))
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

	( @iter $index:expr, $index_ident:ident, $objectname:ident, $args_iter:ident, $name:ident ( $( $names:ident : $params:ty ),* ) $( -> $returns:ty )* => $body:tt $($tail:tt)*) => (
		if $index_ident == $index {
			{ marshall!($args_iter, $objectname, ( $( $names : $params ),* ) $( -> $returns )* => $body) }
		}
		dispatch_fn!( @iter $index + 1, $index_ident, $objectname, $args_iter $($tail)*)
	);

	( $index_ident:ident, $objectname:ident, $args_iter:ident, $($tail:tt)* ) => (
		dispatch_fn!( @iter 0, $index_ident, $objectname, $args_iter, $($tail)*);
	);
}

#[macro_export]
macro_rules! impl_function_executor {
	( $objectname:ident : $structname:ty,
	  $( $name:ident ( $( $names:ident : $params:ty ),* ) $( -> $returns:ty )* => $body:tt , )*
	  => $($pre:tt)+ ) => (
		impl $( $pre ) + $structname {
			#[allow(unused)]
			fn resolver() -> &'static $crate::wasmi::ModuleImportResolver {
				struct Resolver;
				impl $crate::wasmi::ModuleImportResolver for Resolver {
					fn resolve_func(&self, name: &str, signature: &$crate::wasmi::Signature) -> ::std::result::Result<$crate::wasmi::FuncRef, $crate::wasmi::Error> {
						resolve_fn!(signature, name, $( $name( $( $params ),* ) $( -> $returns )* => )*);

						Err($crate::wasmi::Error::Instantiation(
							format!("Export {} not found", name),
						))
					}
				}
				&Resolver
			}
		}

		impl $( $pre ) + $crate::wasmi::Externals for $structname {
			fn invoke_index(
				&mut self,
				index: usize,
				args: $crate::wasmi::RuntimeArgs,
			) -> ::std::result::Result<Option<$crate::wasmi::RuntimeValue>, $crate::wasmi::Trap> {
				let $objectname = self;
				let mut args = args.as_ref().iter();
				dispatch_fn!(index, $objectname, args, $( $name( $( $names : $params ),* ) $( -> $returns )* => $body ),*);
			}
		}
	);
}
