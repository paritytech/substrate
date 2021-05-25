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

//! Definition of macros that hides boilerplate of defining external environment
//! for a wasm module.
//!
//! Most likely you should use `define_env` macro.

macro_rules! convert_args {
	() => (vec![]);
	( $( $t:ty ),* ) => ( vec![ $( { use $crate::wasm::env_def::ConvertibleToWasm; <$t>::VALUE_TYPE }, )* ] );
}

macro_rules! gen_signature {
	( ( $( $params: ty ),* ) ) => (
		{
			parity_wasm::elements::FunctionType::new(convert_args!($($params),*), vec![])
		}
	);

	( ( $( $params: ty ),* ) -> $returns: ty ) => (
		{
			parity_wasm::elements::FunctionType::new(convert_args!($($params),*), vec![{
				use $crate::wasm::env_def::ConvertibleToWasm; <$returns>::VALUE_TYPE
			}])
		}
	);
}

macro_rules! gen_signature_dispatch {
	(
		$needle_module:ident,
		$needle_name:ident,
		$needle_sig:ident ;
		$module:ident,
		$name:ident
		( $ctx:ident $( , $names:ident : $params:ty )* ) $( -> $returns:ty )* , $($rest:tt)*
	) => {
		let module = stringify!($module).as_bytes();
		if module == $needle_module && stringify!($name).as_bytes() == $needle_name {
			let signature = gen_signature!( ( $( $params ),* ) $( -> $returns )* );
			if $needle_sig == &signature {
				return true;
			}
		} else {
			gen_signature_dispatch!($needle_module, $needle_name, $needle_sig ; $($rest)*);
		}
	};
	( $needle_module:ident, $needle_name:ident, $needle_sig:ident ; ) => {};
}

/// Unmarshall arguments and then execute `body` expression and return its result.
macro_rules! unmarshall_then_body {
	( $body:tt, $ctx:ident, $args_iter:ident, $( $names:ident : $params:ty ),* ) => ({
		$(
			let $names : <$params as $crate::wasm::env_def::ConvertibleToWasm>::NativeType =
				$args_iter.next()
					.and_then(|v| <$params as $crate::wasm::env_def::ConvertibleToWasm>
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
	F: FnOnce() -> Result<R, crate::wasm::runtime::TrapReason>,
{
	f
}

macro_rules! unmarshall_then_body_then_marshall {
	( $args_iter:ident, $ctx:ident, ( $( $names:ident : $params:ty ),* ) -> $returns:ty => $body:tt ) => ({
		let body = $crate::wasm::env_def::macros::constrain_closure::<
			<$returns as $crate::wasm::env_def::ConvertibleToWasm>::NativeType, _
		>(|| {
			unmarshall_then_body!($body, $ctx, $args_iter, $( $names : $params ),*)
		});
		let r = body().map_err(|reason| {
			$ctx.set_trap_reason(reason);
			sp_sandbox::HostError
		})?;
		return Ok(sp_sandbox::ReturnValue::Value({ use $crate::wasm::env_def::ConvertibleToWasm; r.to_typed_value() }))
	});
	( $args_iter:ident, $ctx:ident, ( $( $names:ident : $params:ty ),* ) => $body:tt ) => ({
		let body = $crate::wasm::env_def::macros::constrain_closure::<(), _>(|| {
			unmarshall_then_body!($body, $ctx, $args_iter, $( $names : $params ),*)
		});
		body().map_err(|reason| {
			$ctx.set_trap_reason(reason);
			sp_sandbox::HostError
		})?;
		return Ok(sp_sandbox::ReturnValue::Unit)
	})
}

macro_rules! define_func {
	( $trait:tt $name:ident ( $ctx: ident $(, $names:ident : $params:ty)*) $(-> $returns:ty)* => $body:tt ) => {
		fn $name< E: $trait >(
			$ctx: &mut $crate::wasm::Runtime<E>,
			args: &[sp_sandbox::Value],
		) -> Result<sp_sandbox::ReturnValue, sp_sandbox::HostError>
			where
				<E::T as frame_system::Config>::AccountId:
					sp_core::crypto::UncheckedFrom<<E::T as frame_system::Config>::Hash> +
						AsRef<[u8]>
		{
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

macro_rules! register_body {
	( $reg_cb:ident, $trait:tt;
		$module:ident $name:ident ( $ctx:ident $( , $names:ident : $params:ty )* )
		$( -> $returns:ty )* => $body:tt
	) => {
		$reg_cb(
			stringify!($module).as_bytes(),
			stringify!($name).as_bytes(),
			{
				define_func!(
					 $trait $name ( $ctx $(, $names : $params )* ) $( -> $returns )* => $body
				);
				$name::<E>
			}
		);
	}
}

macro_rules! register_func {
	( $reg_cb:ident, $trait:tt; ) => {};

	( $reg_cb:ident, $trait:tt;
		__unstable__ $name:ident ( $ctx:ident $( , $names:ident : $params:ty )* )
		$( -> $returns:ty )* => $body:tt $($rest:tt)*
	) => {
		#[cfg(feature = "unstable-interface")]
		register_body!(
			$reg_cb, $trait;
			__unstable__ $name
			( $ctx $( , $names : $params )* )
			$( -> $returns )* => $body
		);
		register_func!( $reg_cb, $trait; $($rest)* );
	};

	( $reg_cb:ident, $trait:tt;
		$module:ident $name:ident ( $ctx:ident $( , $names:ident : $params:ty )* )
		$( -> $returns:ty )* => $body:tt $($rest:tt)*
	) => {
		register_body!(
			$reg_cb, $trait;
			$module $name
			( $ctx $( , $names : $params )* )
			$( -> $returns )* => $body
		);
		register_func!( $reg_cb, $trait; $($rest)* );
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
	( $init_name:ident , < E: $trait:tt > ,
		$( [$module:ident] $name:ident ( $ctx:ident $( , $names:ident : $params:ty )* )
			$( -> $returns:ty )* => $body:tt , )*
	) => {
		pub struct $init_name;

		impl $crate::wasm::env_def::ImportSatisfyCheck for $init_name {
			fn can_satisfy(module: &[u8], name: &[u8], func_type: &parity_wasm::elements::FunctionType) -> bool {
				#[cfg(not(feature = "unstable-interface"))]
				if module == b"__unstable__" {
					return false;
				}
				gen_signature_dispatch!(
					module, name, func_type ;
					$( $module, $name ( $ctx $(, $names : $params )* ) $( -> $returns )* , )*
				);

				return false;
			}
		}

		impl<E: Ext> $crate::wasm::env_def::FunctionImplProvider<E> for $init_name
		where
			<E::T as frame_system::Config>::AccountId:
				sp_core::crypto::UncheckedFrom<<E::T as frame_system::Config>::Hash> +
					AsRef<[u8]>
		{
			fn impls<F: FnMut(&[u8], &[u8], $crate::wasm::env_def::HostFunc<E>)>(f: &mut F) {
				register_func!(
					f,
					$trait;
					$( $module $name ( $ctx $( , $names : $params )* ) $( -> $returns)* => $body )*
				);
			}
		}
	};
}

#[cfg(test)]
mod tests {
	use parity_wasm::elements::FunctionType;
	use parity_wasm::elements::ValueType;
	use sp_runtime::traits::Zero;
	use sp_sandbox::{ReturnValue, Value};
	use crate::{
		Weight,
		wasm::{Runtime, runtime::TrapReason, tests::MockExt},
		exec::Ext,
	};

	struct TestRuntime {
		value: u32,
	}

	impl TestRuntime {
		fn set_trap_reason(&mut self, _reason: TrapReason) {}
	}

	#[test]
	fn macro_unmarshall_then_body_then_marshall_value_or_trap() {
		fn test_value(
			_ctx: &mut TestRuntime,
			args: &[sp_sandbox::Value],
		) -> Result<ReturnValue, sp_sandbox::HostError> {
			let mut args = args.iter();
			unmarshall_then_body_then_marshall!(
				args,
				_ctx,
				(a: u32, b: u32) -> u32 => {
					if b == 0 {
						Err(crate::wasm::runtime::TrapReason::Termination)
					} else {
						Ok(a / b)
					}
				}
			)
		}

		let ctx = &mut TestRuntime { value: 0 };
		assert_eq!(
			test_value(ctx, &[Value::I32(15), Value::I32(3)]).unwrap(),
			ReturnValue::Value(Value::I32(5)),
		);
		assert!(test_value(ctx, &[Value::I32(15), Value::I32(0)]).is_err());
	}

	#[test]
	fn macro_unmarshall_then_body_then_marshall_unit() {
		fn test_unit(
			ctx: &mut TestRuntime,
			args: &[sp_sandbox::Value],
		) -> Result<ReturnValue, sp_sandbox::HostError> {
			let mut args = args.iter();
			unmarshall_then_body_then_marshall!(
				args,
				ctx,
				(a: u32, b: u32) => {
					ctx.value = a + b;
					Ok(())
				}
			)
		}

		let ctx = &mut TestRuntime { value: 0 };
		let result = test_unit(ctx, &[Value::I32(2), Value::I32(3)]).unwrap();
		assert_eq!(result, ReturnValue::Unit);
		assert_eq!(ctx.value, 5);
	}

	#[test]
	fn macro_define_func() {
		define_func!( Ext seal_gas (_ctx, amount: u32) => {
			let amount = Weight::from(amount);
			if !amount.is_zero() {
				Ok(())
			} else {
				Err(TrapReason::Termination)
			}
		});
		let _f: fn(&mut Runtime<MockExt>, &[sp_sandbox::Value])
			-> Result<sp_sandbox::ReturnValue, sp_sandbox::HostError> = seal_gas::<MockExt>;
	}

	#[test]
	fn macro_gen_signature() {
		assert_eq!(
			gen_signature!((i32)),
			FunctionType::new(vec![ValueType::I32], vec![]),
		);

		assert_eq!(
			gen_signature!( (i32, u32) -> u32 ),
			FunctionType::new(vec![ValueType::I32, ValueType::I32], vec![ValueType::I32]),
		);
	}

	#[test]
	fn macro_unmarshall_then_body() {
		let args = vec![Value::I32(5), Value::I32(3)];
		let mut args = args.iter();

		let ctx: &mut u32 = &mut 0;

		let r = unmarshall_then_body!(
			{
				*ctx = a + b;
				a * b
			},
			ctx,
			args,
			a: u32,
			b: u32
		);

		assert_eq!(*ctx, 8);
		assert_eq!(r, 15);
	}

	#[test]
	fn macro_define_env() {
		use crate::wasm::env_def::ImportSatisfyCheck;

		define_env!(Env, <E: Ext>,
			[seal0] seal_gas( _ctx, amount: u32 ) => {
				let amount = Weight::from(amount);
				if !amount.is_zero() {
					Ok(())
				} else {
					Err(crate::wasm::runtime::TrapReason::Termination)
				}
			},
		);

		assert!(
			Env::can_satisfy(b"seal0", b"seal_gas",&FunctionType::new(vec![ValueType::I32], vec![]))
		);
		assert!(
			!Env::can_satisfy(b"seal0", b"not_exists", &FunctionType::new(vec![], vec![]))
		);
	}
}
