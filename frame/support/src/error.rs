// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Macro for declaring a module error.

#[doc(hidden)]
pub use sp_runtime::traits::{BadOrigin, LookupError};

/// Declare an error type for a runtime module.
///
/// `decl_error!` supports only variants that do not hold any data. The dispatchable
/// functions return [`DispatchResult`](sp_runtime::DispatchResult). The error type
/// implements `From<ErrorType> for DispatchResult` to make the error type usable as error
/// in the dispatchable functions.
///
/// It is required that the error type is registered in `decl_module!` to make the error
/// exported in the metadata.
///
/// # Usage
///
/// ```
/// # use frame_support::{decl_error, decl_module};
/// #
/// decl_error! {
///     /// Errors that can occur in my module.
///     pub enum MyError for Module<T: Config> {
///         /// Hey this is an error message that indicates bla.
///         MyCoolErrorMessage,
///         /// You are just not cool enough for my module!
///         YouAreNotCoolEnough,
///     }
/// }
///
/// # use frame_system::Config;
///
/// // You need to register the error type in `decl_module!` as well to make the error
/// // exported in the metadata.
///
/// decl_module! {
///     pub struct Module<T: Config> for enum Call where origin: T::Origin {
///         type Error = MyError<T>;
///
///         #[weight = 0]
///         fn do_something(origin) -> frame_support::dispatch::DispatchResult {
///             Err(MyError::<T>::YouAreNotCoolEnough.into())
///         }
///     }
/// }
///
/// # fn main() {}
/// ```
///
/// For instantiable modules you also need to give the instance generic type and bound to the
/// error declaration.
#[macro_export]
macro_rules! decl_error {
	(
		$(#[$attr:meta])*
		pub enum $error:ident
			for $module:ident<
				$generic:ident: $trait:path
				$(, $inst_generic:ident: $instance:path)?
			>
			$( where $( $where_ty:ty: $where_bound:path ),* $(,)? )?
		{
			$(
				$( #[doc = $doc_attr:tt] )*
				$name:ident
			),*
			$(,)?
		}
	) => {
		$(#[$attr])*
		#[derive(
			$crate::codec::Encode,
			$crate::codec::Decode,
			$crate::scale_info::TypeInfo,
			$crate::PalletError,
		)]
		#[scale_info(skip_type_params($generic $(, $inst_generic)?), capture_docs = "always")]
		pub enum $error<$generic: $trait $(, $inst_generic: $instance)?>
		$( where $( $where_ty: $where_bound ),* )?
		{
			#[doc(hidden)]
			#[codec(skip)]
			__Ignore(
				$crate::sp_std::marker::PhantomData<($generic, $( $inst_generic)?)>,
				$crate::Never,
			),
			$(
				$( #[doc = $doc_attr] )*
				$name
			),*
		}

		impl<$generic: $trait $(, $inst_generic: $instance)?> $crate::sp_std::fmt::Debug
			for $error<$generic $(, $inst_generic)?>
		$( where $( $where_ty: $where_bound ),* )?
		{
			fn fmt(&self, f: &mut $crate::sp_std::fmt::Formatter<'_>) -> $crate::sp_std::fmt::Result {
				f.write_str(self.as_str())
			}
		}

		impl<$generic: $trait $(, $inst_generic: $instance)?> $error<$generic $(, $inst_generic)?>
		$( where $( $where_ty: $where_bound ),* )?
		{
			fn as_str(&self) -> &'static str {
				match self {
					Self::__Ignore(_, _) => unreachable!("`__Ignore` can never be constructed"),
					$(
						$error::$name => stringify!($name),
					)*
				}
			}
		}

		impl<$generic: $trait $(, $inst_generic: $instance)?> From<$error<$generic $(, $inst_generic)?>>
			for &'static str
		$( where $( $where_ty: $where_bound ),* )?
		{
			fn from(err: $error<$generic $(, $inst_generic)?>) -> &'static str {
				err.as_str()
			}
		}

		impl<$generic: $trait $(, $inst_generic: $instance)?> From<$error<$generic $(, $inst_generic)?>>
			for $crate::sp_runtime::DispatchError
		$( where $( $where_ty: $where_bound ),* )?
		{
			fn from(err: $error<$generic $(, $inst_generic)?>) -> Self {
				use $crate::codec::Encode;
				let index = <$generic::PalletInfo as $crate::traits::PalletInfo>
					::index::<$module<$generic $(, $inst_generic)?>>()
					.expect("Every active module has an index in the runtime; qed") as u8;
				let mut error = err.encode();
				error.resize($crate::MAX_MODULE_ERROR_ENCODED_SIZE, 0);

				$crate::sp_runtime::DispatchError::Module($crate::sp_runtime::ModuleError {
					index,
					error: TryInto::try_into(error).expect("encoded error is resized to be equal to the maximum encoded error size; qed"),
					message: Some(err.as_str()),
				})
			}
		}
	};
}
