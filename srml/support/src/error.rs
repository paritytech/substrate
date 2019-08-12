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

#[macro_export]
macro_rules! decl_error {
	(
		$(#[$attr:meta])*
		pub enum $error:ident {
			$(
				$( #[$variant_attr:meta] )*
				$name:ident
			),*
			$(,)?
		}
	) => {
		#[derive(Clone, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug))]
		$(#[$attr])*
		pub enum $error {
			Other(&'static str),
			$(
				$(#[$variant_attr])*
				$name
			),*
		}

		impl $crate::ModuleDispatchError for $error {
			fn as_u8(&self) -> u8 {
				$crate::decl_error! {
					@GENERATE_AS_U8
					self
					$error
					{}
					1,
					$( $name ),*
				}
			}

			fn as_str(&self) -> &'static str {
				match self {
					$error::Other(err) => err,
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
			$( $generated )*
		}
	}
}
