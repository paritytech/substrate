// Copyright 2018 Parity Technologies (UK) Ltd.
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
//! Typically you should use `define_env` macro.

#[macro_export]
macro_rules! convert_args {
	() => (vec![]);
	( $( $t:ty ),* ) => ( vec![ $( { use $crate::vm::env_def::ConvertibleToWasm; <$t>::VALUE_TYPE }, )* ] );
}

#[macro_export]
macro_rules! gen_signature {
	( ( $( $params: ty ),* ) ) => (
		{
			FunctionType::new(convert_args!($($params),*), None)
		}
	);

	( ( $( $params: ty ),* ) -> $returns: ty ) => (
		{
			FunctionType::new(convert_args!($($params),*), Some({
				use $crate::vm::env_def::ConvertibleToWasm; <$returns>::VALUE_TYPE
			}))
		}
	);
}

/// Unmarshall arguments and then execute `body` expression and return its result.
macro_rules! unmarshall_then_body {
	( $body:tt, $ctx:ident, $args_iter:ident, $( $names:ident : $params:ty ),* ) => ({
		$(
			let $names : <$params as $crate::vm::env_def::ConvertibleToWasm>::NativeType =
				$args_iter.next()
					.and_then(|v| <$params as $crate::vm::env_def::ConvertibleToWasm>
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
/// ```rust,ignore
/// let f: FnOnce() -> Result<<u32 as ConvertibleToWasm>::NativeType, _> = || { /* ... */ };
/// ```
///
/// we use this function to constrain the type of the closure.
#[inline(always)]
pub fn constrain_closure<R, F>(f: F) -> F
where
	F: FnOnce() -> Result<R, ::sandbox::HostError>,
{
	f
}

#[macro_export]
macro_rules! unmarshall_then_body_then_marshall {
	( $args_iter:ident, $ctx:ident, ( $( $names:ident : $params:ty ),* ) -> $returns:ty => $body:tt ) => ({
		let body = $crate::vm::env_def::macros::constrain_closure::<
			<$returns as $crate::vm::env_def::ConvertibleToWasm>::NativeType, _
		>(|| {
			unmarshall_then_body!($body, $ctx, $args_iter, $( $names : $params ),*)
		});
		let r = body()?;
		return Ok($crate::sandbox::ReturnValue::Value({ use $crate::vm::env_def::ConvertibleToWasm; r.to_typed_value() }))
	});
	( $args_iter:ident, $ctx:ident, ( $( $names:ident : $params:ty ),* ) => $body:tt ) => ({
		let body = $crate::vm::env_def::macros::constrain_closure::<(), _>(|| {
			unmarshall_then_body!($body, $ctx, $args_iter, $( $names : $params ),*)
		});
		body()?;
		return Ok($crate::sandbox::ReturnValue::Unit)
	})
}

#[macro_export]
macro_rules! define_func {
	( < E: $ext_ty:tt > $name:ident ( $ctx: ident $(, $names:ident : $params:ty)*) $(-> $returns:ty)* => $body:tt ) => {
		fn $name< E: $ext_ty >(
			$ctx: &mut $crate::vm::Runtime<E>,
			args: &[$crate::sandbox::TypedValue],
		) -> Result<sandbox::ReturnValue, sandbox::HostError> {
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

/// Define a function set that can be imported by executing wasm code.
///
/// **NB**: Be advised that all functions defined by this macro
/// will panic if called with unexpected arguments.
///
/// It's up to the user of this macro to check signatures of wasm code to be executed
/// and reject the code if any imported function has a mismached signature.
macro_rules! define_env {
	( $init_name:ident , < E: $ext_ty:tt > ,
		$( $name:ident ( $ctx:ident $( , $names:ident : $params:ty )* )
			$( -> $returns:ty )* => $body:tt , )*
	) => {
		pub(crate) fn $init_name<E: Ext>() -> HostFunctionSet<E> {
			let mut env = HostFunctionSet::new();

			$(
				env.funcs.insert(
					stringify!( $name ).into(),
					HostFunction::new(
						gen_signature!( ( $( $params ),* ) $( -> $returns )* ),
						{
							define_func!(
								< E: $ext_ty > $name ( $ctx $(, $names : $params )* ) $( -> $returns )* => $body
							);
							$name::<E>
						},
					),
				);
			)*

			env
		}
	};
}

#[cfg(test)]
mod tests {
	use parity_wasm::elements::FunctionType;
	use parity_wasm::elements::ValueType;
	use runtime_primitives::traits::{As, Zero};
	use sandbox::{self, ReturnValue, TypedValue};
	use vm::env_def::{HostFunction, HostFunctionSet};
	use vm::tests::MockExt;
	use vm::{Ext, Runtime};
	use Trait;

	#[test]
	fn macro_unmarshall_then_body_then_marshall_value_or_trap() {
		fn test_value(
			_ctx: &mut u32,
			args: &[sandbox::TypedValue],
		) -> Result<ReturnValue, sandbox::HostError> {
			let mut args = args.iter();
			unmarshall_then_body_then_marshall!(
				args,
				_ctx,
				(a: u32, b: u32) -> u32 => {
					if b == 0 {
						Err(sandbox::HostError)
					} else {
						Ok(a / b)
					}
				}
			)
		}

		let ctx = &mut 0;
		assert_eq!(
			test_value(ctx, &[TypedValue::I32(15), TypedValue::I32(3)]).unwrap(),
			ReturnValue::Value(TypedValue::I32(5)),
		);
		assert!(test_value(ctx, &[TypedValue::I32(15), TypedValue::I32(0)]).is_err());
	}

	#[test]
	fn macro_unmarshall_then_body_then_marshall_unit() {
		fn test_unit(
			ctx: &mut u32,
			args: &[sandbox::TypedValue],
		) -> Result<ReturnValue, sandbox::HostError> {
			let mut args = args.iter();
			unmarshall_then_body_then_marshall!(
				args,
				ctx,
				(a: u32, b: u32) => {
					*ctx = a + b;
					Ok(())
				}
			)
		}

		let ctx = &mut 0;
		let result = test_unit(ctx, &[TypedValue::I32(2), TypedValue::I32(3)]).unwrap();
		assert_eq!(result, ReturnValue::Unit);
		assert_eq!(*ctx, 5);
	}

	#[test]
	fn macro_define_func() {
		define_func!( <E: Ext> ext_gas (_ctx, amount: u32) => {
			let amount = <<<E as Ext>::T as Trait>::Gas as As<u32>>::sa(amount);
			if !amount.is_zero() {
				Ok(())
			} else {
				Err(sandbox::HostError)
			}
		});
		let _f: fn(&mut Runtime<MockExt>, &[sandbox::TypedValue])
			-> Result<sandbox::ReturnValue, sandbox::HostError> = ext_gas::<MockExt>;
	}

	#[test]
	fn macro_gen_signature() {
		assert_eq!(
			gen_signature!((i32)),
			FunctionType::new(vec![ValueType::I32], None),
		);

		assert_eq!(
			gen_signature!( (i32, u32) -> u32 ),
			FunctionType::new(vec![ValueType::I32, ValueType::I32], Some(ValueType::I32)),
		);
	}

	#[test]
	fn macro_unmarshall_then_body() {
		let args = vec![TypedValue::I32(5), TypedValue::I32(3)];
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
		define_env!(init_env, <E: Ext>,
			ext_gas( _ctx, amount: u32 ) => {
				let amount = <<<E as Ext>::T as Trait>::Gas as As<u32>>::sa(amount);
				if !amount.is_zero() {
					Ok(())
				} else {
					Err(sandbox::HostError)
				}
			},
		);

		let env = init_env::<MockExt>();
		assert!(env.funcs.get("ext_gas").is_some());
	}
}
