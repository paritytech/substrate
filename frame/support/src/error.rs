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
/// Optionally the macro can generate variants for system errors through the attribute:
/// `#[substrate(impl_from_frame_system($FrameSystemCrate))]`.
/// This will generate three more variants `SystemRequiresSignedOrigin`,
/// `SystemRequiresRootOrigin`, `SystemRequiresNoOrigin` and implement
/// `From<frame_system::Error>`.
///
/// `decl_error!` supports only variants that do not hold any data.
///
/// # Usage
///
/// ```
/// # use frame_support::{decl_error, decl_module};
/// decl_error! {
///     /// Errors that can occur in my module.
///     #[substrate(impl_from_frame_system(frame_system))]
///     pub enum MyError {
///         /// Hey this is an error message that indicates bla.
///         MyCoolErrorMessage,
///         /// You are just not cool enough for my module!
///         YouAreNotCoolEnough,
///     }
/// }
///
/// # use frame_system::{self as system, Trait, ensure_signed};
///
/// // You need to register the error type in `decl_module!` as well.
///
/// decl_module! {
///     pub struct Module<T: Trait> for enum Call where origin: T::Origin {
///         type Error = MyError;
///
///         fn do_something(origin) -> Result<(), MyError> {
///             Err(MyError::YouAreNotCoolEnough)
///         }
///     }
/// }
///
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! decl_error {
	(
		$( #[ $( $attr:tt )* ] )*
		pub enum $error:ident {
			$(
				$( #[doc = $doc_attr:tt] )*
				$name:ident
			),*
			$(,)?
		}
	) => {
		$crate::decl_error! {@parse_top_attr
			top_attr_parsed {}
			impl_from_frame_system {}
			$( #[ $( $attr )* ] )*
			pub enum $error {
				$(
					$( #[doc = $doc_attr] )*
					$name
				),*
			}
		}
	};
	// Parse top attr: impl_from_frame_system
	(@parse_top_attr
		top_attr_parsed { $( $top_attr_parsed:tt )*}
		impl_from_frame_system {}
		#[substrate(impl_from_frame_system($frame_system:ident))]
		$( #[ $( $attr:tt )* ] )*
		pub enum $error:ident {
			$(
				$( #[doc = $doc_attr:tt] )*
				$name:ident
			),*
		}
	) => {
		$crate::decl_error! {@parse_top_attr
			top_attr_parsed { $( $top_attr_parsed )* }
			impl_from_frame_system { $frame_system }
			$( #[ $( $attr )* ] )*
			pub enum $error {
				/// Frame system requires a signed origin,
				SystemRequiresSignedOrigin,
				/// Frame system requires a root origin,
				SystemRequiresRootOrigin,
				/// Frame system requires no origin,
				SystemRequiresNoOrigin,
				$(
					$( #[doc = $doc_attr] )*
					$name
				),*
			}
		}
	};
	// Parse top attr: invalid substrate attribute
	(@parse_top_attr
		top_attr_parsed { $( $top_attr_parsed:tt )*}
		impl_from_frame_system {}
		#[substrate($($invalid:tt)*)]
		$( #[ $( $attr:tt )* ] )*
		pub enum $error:ident {
			$(
				$( #[doc = $doc_attr:tt] )*
				$name:ident
			),*
		}
	) => {
		compile_error!(
			concat!(
				"Invalid substrate attribute: `#[substrate(",
				$( stringify!($invalid), )*
				")]`",
			)
		);
	};
	// Parse top attr: other meta attribute
	(@parse_top_attr
		top_attr_parsed { $( $top_attr_parsed:tt )* }
		impl_from_frame_system { $( $frame_system:ident )?}
		#[$first_attr:meta]
		$( #[ $( $attr:tt )* ] )*
		pub enum $error:ident {
			$(
				$( #[doc = $doc_attr:tt] )*
				$name:ident
			),*
		}
	) => {
		$crate::decl_error! {@parse_top_attr
			top_attr_parsed { $( $top_attr_parsed )* #[$first_attr] }
			impl_from_frame_system { $( $frame_system )? }
			$( #[ $( $attr )* ] )*
			pub enum $error {
				$(
					$( #[doc = $doc_attr] )*
					$name
				),*
			}
		}
	};
	// All parsed: implementation
	(@parse_top_attr
		top_attr_parsed { $( #[$attr:meta] )* }
		impl_from_frame_system { $( $system:ident )?}
		pub enum $error:ident {
			$(
				$( #[doc = $doc_attr:tt] )*
				$name:ident
			),*
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

		$(
			impl From<$system::Error> for $error {
				fn from(val: $system::Error) -> $error {
					match val {
						$system::Error::CannotLookup => $error::CannotLookup,
						$system::Error::RequireSignedOrigin => $error::SystemRequiresSignedOrigin,
						$system::Error::RequireSignedOrigin => $error::SystemRequiresSignedOrigin,
						$system::Error::RequireRootOrigin => $error::SystemRequiresRootOrigin,
						$system::Error::RequireNoOrigin => $error::SystemRequiresNoOrigin,
						$system::Error::Other(e) => $error::Other(e),
					}
				}
			}
		)?

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
