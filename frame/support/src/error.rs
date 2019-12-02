// Copyright 2019 Parity Technologies (UK) Ltd.
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
pub use sp_runtime::traits::LookupError;
pub use frame_metadata::{ModuleErrorMetadata, ErrorMetadata, DecodeDifferent};

/// Declare an error type for a runtime module.
///
/// The generated error type inherently has the variants `Other` and `CannotLookup`. `Other` can
/// hold any `&'static str` error message and is present for convenience/backward compatibility.
/// The `CannotLookup` variant indicates that some lookup could not be done. For both variants the
/// error type implements `From<&'static str>` and `From<LookupError>` to make them usable with the
/// try operator.
///
/// # Usage
///
/// ```
/// # use frame_support::decl_error;
/// decl_error! {
///     /// Errors that can occur in my module.
///     pub enum MyError {
///         /// Hey this is an error message that indicates bla.
///         MyCoolErrorMessage,
///         /// You are just not cool enough for my module!
///         YouAreNotCoolEnough,
///     }
/// }
/// ```
///
/// `decl_error!` supports only variants that do not hold any data.
#[macro_export]
macro_rules! decl_error {
	(
		$(#[$attr:meta])*
		pub enum $error:ident {
			$(
				$( #[doc = $doc_attr:tt] )*
				$name:ident
			),*
			$(,)?
		}
	) => {
		#[derive(Clone, PartialEq, Eq, $crate::RuntimeDebug)]
		$(#[$attr])*
		pub enum $error {
			Other(&'static str),
			CannotLookup,
			$(
				$( #[doc = $doc_attr] )*
				$name
			),*
		}

		impl $crate::dispatch::ModuleDispatchError for $error {
			fn as_u8(&self) -> u8 {
				$crate::decl_error! {
					@GENERATE_AS_U8
					self
					$error
					{}
					2,
					$( $name ),*
				}
			}

			fn as_str(&self) -> &'static str {
				match self {
					$error::Other(err) => err,
					$error::CannotLookup => "Can not lookup",
					$(
						$error::$name => stringify!($name),
					)*
				}
			}
		}

		impl From<&'static str> for $error {
			fn from(val: &'static str) -> $error {
				$error::Other(val)
			}
		}

		impl From<$crate::error::LookupError> for $error {
			fn from(_: $crate::error::LookupError) -> $error {
				$error::CannotLookup
			}
		}

		impl From<$error> for &'static str {
			fn from(err: $error) -> &'static str {
				use $crate::dispatch::ModuleDispatchError;
				err.as_str()
			}
		}

		impl Into<$crate::dispatch::DispatchError> for $error {
			fn into(self) -> $crate::dispatch::DispatchError {
				use $crate::dispatch::ModuleDispatchError;
				$crate::dispatch::DispatchError::new(None, self.as_u8(), Some(self.as_str()))
			}
		}

		impl $crate::error::ModuleErrorMetadata for $error {
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
			$error::Other(_) => 0,
			$error::CannotLookup => 1,
			$( $generated )*
		}
	}
}
