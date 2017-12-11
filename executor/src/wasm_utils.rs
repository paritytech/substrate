// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Rust implementation of Polkadot contracts.

use std::sync::{Arc, Weak};
pub use std::result;
pub use parity_wasm::elements::{ValueType};
pub use parity_wasm::interpreter::{RuntimeValue, UserFunctionDescriptor, UserFunctionExecutor,
	CallerContext, UserDefinedElements, Error, native_module};
pub use parity_wasm::{builder, ProgramInstance, ModuleInstance};

pub fn program_with_externals<E: UserFunctionExecutor + 'static>(externals: UserDefinedElements<E>, module_name: &str) -> result::Result<ProgramInstance, Error> {
	let program = ProgramInstance::new();
	let instance = {
		let module = builder::module().build();
		let mut instance = ModuleInstance::new(Weak::default(), module_name.into(), module)?;
		instance.instantiate(None)?;
		instance
	};
	let other_instance = native_module(Arc::new(instance), externals)?;
	program.insert_loaded_module(module_name, other_instance)?;
	Ok(program)
}

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
	( $context:ident, $self:ident, ( $( $names:ident : $params:ty ),* ) -> $returns:ty => $body:tt ) => ({
		let r : <$returns as $crate::wasm_utils::ConvertibleToWasm>::NativeType = reverse_params!($body, $self, $context, $( $names : $params ),*);
		Ok(Some({ use $crate::wasm_utils::ConvertibleToWasm; r.to_runtime_value() }))
	});
	( $context:ident, $self:ident, ( $( $names:ident : $params:ty ),* ) => $body:tt ) => ({
		reverse_params!($body, $self, $context, $( $names : $params ),*);
		Ok(None)
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
				n => Err($crate::wasm_utils::Error::Trap(format!("not implemented: {}", n)).into())
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

#[macro_export]
macro_rules! function_executor {
	( $objectname:ident : $structname:ident, $( $name:ident ( $( $names:ident : $params:ty ),* ) $( -> $returns:ty )* => $body:tt ),* ) => (
		impl $crate::wasm_utils::UserFunctionExecutor for $structname {
			dispatch!($objectname, $( $name( $( $names : $params ),* ) $( -> $returns )* => $body ),*);
		}
		impl $structname {
			signatures!($( $name( $( $params ),* ) $( -> $returns )* ),*);
		}
	);
}
