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

//! Rust implementation of Substrate contracts.

use std::sync::{Arc};
use std::collections::HashMap;
pub use std::result;
pub use parity_wasm::builder;
pub use parity_wasm::elements::{ValueType, Module};
pub use parity_wasm::interpreter::{RuntimeValue, UserFunctionDescriptor, UserFunctionExecutor,
	UserDefinedElements, env_native_module, DummyUserError, ExecutionParams, UserError};
use parity_wasm::interpreter;

pub type Error = interpreter::Error<DummyUserError>;
pub type MemoryInstance = interpreter::MemoryInstance<DummyUserError>;
pub type CallerContext<'a> = interpreter::CallerContext<'a, DummyUserError>;

pub trait ConvertibleToWasm { const VALUE_TYPE: ValueType; type NativeType; fn to_runtime_value(self) -> RuntimeValue; }
impl ConvertibleToWasm for i32 { type NativeType = i32; const VALUE_TYPE: ValueType = ValueType::I32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I32(self) } }
impl ConvertibleToWasm for u32 { type NativeType = u32; const VALUE_TYPE: ValueType = ValueType::I32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I32(self as i32) } }
impl ConvertibleToWasm for i64 { type NativeType = i64; const VALUE_TYPE: ValueType = ValueType::I64; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I64(self) } }
impl ConvertibleToWasm for u64 { type NativeType = u64; const VALUE_TYPE: ValueType = ValueType::I64; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::I64(self as i64) } }
impl ConvertibleToWasm for f32 { type NativeType = f32; const VALUE_TYPE: ValueType = ValueType::F32; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::F32(self) } }
impl ConvertibleToWasm for f64 { type NativeType = f64; const VALUE_TYPE: ValueType = ValueType::F64; fn to_runtime_value(self) -> RuntimeValue { RuntimeValue::F64(self) } }
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
macro_rules! convert_fn {
	( $name:ident ( $( $params:ty ),* ) ) => ( $crate::wasm_utils::UserFunctionDescriptor::Static(stringify!($name), &convert_args!($($params),*), None) );
	( $name:ident ( $( $params:ty ),* ) -> $returns:ty ) => ( $crate::wasm_utils::UserFunctionDescriptor::Static(stringify!($name), &convert_args!($($params),*), Some({ use $crate::wasm_utils::ConvertibleToWasm; <$returns>::VALUE_TYPE }) ) );
}

#[macro_export]
macro_rules! reverse_params {
	// Entry point, use brackets to recursively reverse above.
	($body:tt, $self:ident, $context:ident, $( $names:ident : $params:ty ),*) => (
		reverse_params!($body $self $context [ $( $names : $params ),* ]);
	);
	($body:tt $self:ident $context:ident [] $( $names:ident : $params:ty ),*) => ({
		$(
			let $names : <$params as $crate::wasm_utils::ConvertibleToWasm>::NativeType = match $context.value_stack.pop_as() {
				Ok(value) => value,
				Err(error) => return Err(error.into()),
			};
		)*
		$body
	});
	($body:tt $self:ident $context:ident [ $name:ident : $param:ty $(, $names:ident : $params:ty )* ] $( $reversed_names:ident : $reversed_params:ty ),*) => (
		reverse_params!($body $self $context [ $( $names : $params ),* ] $name : $param $( , $reversed_names : $reversed_params )*);
	);
}

#[macro_export]
macro_rules! marshall {
	( $context:ident, $self:ident, ( $( $names:ident : $params:ty ),* ) => $body:tt ) => ({
		reverse_params!($body, $self, $context, $( $names : $params ),*);
		Ok(None)
	});
	( $context:ident, $self:ident, ( $( $names:ident : $params:ty ),* ) -> $returns:ty => $body:tt ) => ({
		let r : <$returns as $crate::wasm_utils::ConvertibleToWasm>::NativeType = reverse_params!($body, $self, $context, $( $names : $params ),*);
		Ok(Some({ use $crate::wasm_utils::ConvertibleToWasm; r.to_runtime_value() }))
	})
}

#[macro_export]
macro_rules! dispatch {
	( $objectname:ident, $( $name:ident ( $( $names:ident : $params:ty ),* ) $( -> $returns:ty )* => $body:tt ),* ) => (
		fn execute(&mut self, name: &str, context: $crate::wasm_utils::CallerContext)
			-> $crate::wasm_utils::result::Result<Option<$crate::wasm_utils::RuntimeValue>, $crate::wasm_utils::Error> {
			let $objectname = self;
			match name {
				$(
					stringify!($name) => marshall!(context, $objectname, ( $( $names : $params ),* ) $( -> $returns )* => $body),
				)*
				_ => panic!()
			}
		}
	);
}

#[macro_export]
macro_rules! signatures {
	( $( $name:ident ( $( $params:ty ),* ) $( -> $returns:ty )* ),* ) => (
		const SIGNATURES: &'static [$crate::wasm_utils::UserFunctionDescriptor] = &[
			$(
				convert_fn!( $name ( $( $params ),* ) $( -> $returns )* ),
			)*
		];
	);
}

pub trait IntoUserDefinedElements {
	fn into_user_defined_elements(&mut self) -> UserDefinedElements<DummyUserError>;
}

#[macro_export]
macro_rules! impl_function_executor {
	( $objectname:ident : $structname:ty, $( $name:ident ( $( $names:ident : $params:ty ),* ) $( -> $returns:ty )* => $body:tt ),* => $($pre:tt)+ ) => (
		impl $($pre)+ $crate::wasm_utils::UserFunctionExecutor<$crate::wasm_utils::DummyUserError> for $structname {
			dispatch!($objectname, $( $name( $( $names : $params ),* ) $( -> $returns )* => $body ),*);
		}
		impl $($pre)+ $structname {
			signatures!($( $name( $( $params ),* ) $( -> $returns )* ),*);
		}
		impl $($pre)+ $crate::wasm_utils::IntoUserDefinedElements for $structname {
			fn into_user_defined_elements(&mut self) -> UserDefinedElements<$crate::wasm_utils::DummyUserError> {
				$crate::wasm_utils::UserDefinedElements {
					executor: Some(self),
					globals: HashMap::new(),	// TODO: provide
					functions: ::std::borrow::Cow::from(Self::SIGNATURES),
				}
			}
		}
	);
}

#[derive(Clone)]
struct DummyUserFunctionExecutor;
impl<E: UserError> interpreter::UserFunctionExecutor<E> for DummyUserFunctionExecutor {
	fn execute(&mut self, _name: &str, _context: interpreter::CallerContext<E>) ->
		result::Result<Option<interpreter::RuntimeValue>, interpreter::Error<E>>
	{
		unimplemented!()
	}
}

pub trait AddModuleWithoutFullDependentInstance {
	fn add_module_by_sigs(
		&self,
		name: &str,
		module: Module,
		functions: HashMap<&str, &'static [UserFunctionDescriptor]>,
	) -> result::Result<Arc<interpreter::ModuleInstance<DummyUserError>>, interpreter::Error<DummyUserError>>;

	fn params_with_external<'a, 'b: 'a>(&'b self, externals_name: &str, externals: &'a mut IntoUserDefinedElements) -> result::Result<ExecutionParams<'a, DummyUserError>, Error>;
}

impl AddModuleWithoutFullDependentInstance for interpreter::ProgramInstance<DummyUserError> {
	fn add_module_by_sigs(
		&self,
		name: &str,
		module: Module,
		functions: HashMap<&str, &'static [UserFunctionDescriptor]>
	) -> result::Result<Arc<interpreter::ModuleInstance<DummyUserError>>, interpreter::Error<DummyUserError>> {
		let mut dufe = vec![DummyUserFunctionExecutor; functions.len()];
		let dufe_refs = dufe.iter_mut().collect::<Vec<_>>();
		let fake_module_map = functions.into_iter()
			.zip(dufe_refs.into_iter())
			.map(|((dep_mod_name, functions), dufe)| -> result::Result<_, interpreter::Error<DummyUserError>> {
				let fake_module = Arc::new(
					interpreter::env_native_module(
						self.module(dep_mod_name).ok_or(DummyUserError)?, UserDefinedElements {
							executor: Some(dufe),
							globals: HashMap::new(),
							functions: ::std::borrow::Cow::from(functions),
						}
					)?
				);
				let fake_module: Arc<interpreter::ModuleInstanceInterface<_>> = fake_module;
				Ok((dep_mod_name.into(), fake_module))
			})
			.collect::<result::Result<HashMap<_, _>, interpreter::Error<DummyUserError>>>()?;
		self.add_module(name, module, Some(&fake_module_map))
	}

	fn params_with_external<'a, 'b: 'a>(&'b self, externals_name: &str, externals: &'a mut IntoUserDefinedElements) -> result::Result<ExecutionParams<'a, DummyUserError>, Error> {
		Ok(interpreter::ExecutionParams::with_external(
			externals_name.into(),
			Arc::new(
				interpreter::env_native_module(
					self.module(externals_name).ok_or(DummyUserError)?,
					externals.into_user_defined_elements()
				)?
			)
		))
	}
}
