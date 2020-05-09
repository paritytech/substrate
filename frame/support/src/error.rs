// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Macro for declaring a module error.

#[doc(hidden)]
pub use sp_runtime::traits::{LookupError, BadOrigin};
#[doc(hidden)]
pub use frame_metadata::{ModuleErrorMetadata, ErrorMetadata, DecodeDifferent};

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
///     pub enum MyError for Module<T: Trait> {
///         /// Hey this is an error message that indicates bla.
///         MyCoolErrorMessage,
///         /// You are just not cool enough for my module!
///         YouAreNotCoolEnough,
///     }
/// }
///
/// # use frame_system::{self as system, Trait};
///
/// // You need to register the error type in `decl_module!` as well to make the error
/// // exported in the metadata.
///
/// decl_module! {
///     pub struct Module<T: Trait> for enum Call where origin: T::Origin {
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
		{
			$(
				$( #[doc = $doc_attr:tt] )*
				$name:ident
			),*
			$(,)?
		}
	) => {
		$(#[$attr])*
		pub enum $error<$generic: $trait $(, $inst_generic: $instance)?> {
			#[doc(hidden)]
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
		{
			fn fmt(&self, f: &mut $crate::sp_std::fmt::Formatter<'_>) -> $crate::sp_std::fmt::Result {
				f.write_str(self.as_str())
			}
		}

		impl<$generic: $trait $(, $inst_generic: $instance)?> $error<$generic $(, $inst_generic)?> {
			fn as_u8(&self) -> u8 {
				$crate::decl_error! {
					@GENERATE_AS_U8
					self
					$error
					{}
					0,
					$( $name ),*
				}
			}

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
		{
			fn from(err: $error<$generic $(, $inst_generic)?>) -> &'static str {
				err.as_str()
			}
		}

		impl<$generic: $trait $(, $inst_generic: $instance)?> From<$error<$generic $(, $inst_generic)?>>
			for $crate::sp_runtime::DispatchError
		{
			fn from(err: $error<$generic $(, $inst_generic)?>) -> Self {
				let index = <$generic::ModuleToIndex as $crate::traits::ModuleToIndex>
					::module_to_index::<$module<$generic $(, $inst_generic)?>>()
					.expect("Every active module has an index in the runtime; qed") as u8;

				$crate::sp_runtime::DispatchError::Module {
					index,
					error: err.as_u8(),
					message: Some(err.as_str()),
				}
			}
		}

		impl<$generic: $trait $(, $inst_generic: $instance)?> $crate::error::ModuleErrorMetadata
			for $error<$generic $(, $inst_generic)?>
		{
			fn metadata() -> &'static [$crate::error::ErrorMetadata] {
				&[
					$(
						$crate::error::ErrorMetadata {
							name: $crate::error::DecodeDifferent::Encode(stringify!($name)),
							documentation: $crate::error::DecodeDifferent::Encode(&[
								$( $doc_attr ),*
							]),
						}
					),*
				]
			}
		}
	};
	(@GENERATE_AS_U8
		$self:ident
		$error:ident
		{ $( $generated:tt )* }
		$index:expr,
		$name:ident
		$( , $rest:ident )*
	) => {
		$crate::decl_error! {
			@GENERATE_AS_U8
			$self
			$error
			{
				$( $generated )*
				$error::$name => $index,
			}
			$index + 1,
			$( $rest ),*
		}
	};
	(@GENERATE_AS_U8
		$self:ident
		$error:ident
		{ $( $generated:tt )* }
		$index:expr,
	) => {
		match $self {
			$error::__Ignore(_, _) => unreachable!("`__Ignore` can never be constructed"),
			$( $generated )*
		}
	}
}
