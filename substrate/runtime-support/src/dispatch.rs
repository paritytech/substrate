// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Dispatch system. Just dispatches calls.

pub use rstd::prelude::Vec;
use rstd::ops;
pub use codec::{Slicable, Input, NonTrivialSlicable};

/// Default public dispatch; assumes a 32-byte ID.
pub struct PublicPass<'a> (&'a [u8; 32]);

const NOBODY: [u8; 32] = [0u8; 32];

impl<'a> PublicPass<'a> {
	/// New instance.
	pub fn unchecked_new(who: &[u8; 32]) -> PublicPass {
		PublicPass(who)
	}

	/// New instance.
	pub fn nobody() -> PublicPass<'static> {
		PublicPass(&NOBODY)
	}

	/// New instance.
	pub fn test(who: &[u8; 32]) -> PublicPass {
		PublicPass(who)
	}
}

impl<'a> ops::Deref for PublicPass<'a> {
	type Target = [u8; 32];
	fn deref(&self) -> &[u8; 32] {
		self.0
	}
}

/// Default privileged dispatch.
pub struct PrivPass (());

impl PrivPass {
	/// New instance.
	pub fn unchecked_new() -> PrivPass { PrivPass(()) }

	/// New instance.
	pub fn test() -> PrivPass { PrivPass(()) }
}

/// Implement a dispatch module to create a pairing of a dispatch trait and enum.
#[macro_export]
macro_rules! impl_dispatch {
	(
		pub mod $mod_name:ident;
		$(
			fn $fn_name:ident(self
				$(
					, $param_name:ident : $param:ty
				)*
			)
			= $id:expr ;
		)*
	) => {
		pub mod $mod_name {
			use super::*;

			#[derive(Clone, Copy, PartialEq, Eq)]
			#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
			#[repr(u32)]
			#[allow(non_camel_case_types)]
			enum Id {
				$(
					#[allow(non_camel_case_types)]
					$fn_name = $id,
				)*
			}

			impl Id {
				/// Derive `Some` value from a `u8`, or `None` if it's invalid.
				fn from_u8(value: u8) -> Option<Id> {
					match value {
						$(
							$id => Some(Id::$fn_name),
						)*
						_ => None,
					}
				}
			}

			#[derive(Clone, PartialEq, Eq)]
			#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
			#[allow(missing_docs)]
			pub enum Call {
				$(
					#[allow(non_camel_case_types)]
					$fn_name ( $( $param ),* )
				,)*
			}

			pub trait Dispatch: Sized {
				$(
					fn $fn_name (self, $( $param_name: $param ),* );
				)*
			}

			impl Call {
				pub fn dispatch<D: Dispatch>(self, d: D) {
					match self {
						$(
							Call::$fn_name( $( $param_name ),* ) =>
								d.$fn_name( $( $param_name ),* ),
						)*
					}
				}
			}

			impl $crate::dispatch::Slicable for Call {
				fn decode<I: $crate::dispatch::Input>(input: &mut I) -> Option<Self> {
					let id = u8::decode(input).and_then(Id::from_u8)?;
					Some(match id {
						$(
							Id::$fn_name => {
								$(
									let $param_name = $crate::dispatch::Slicable::decode(input)?;
								)*
								Call :: $fn_name( $( $param_name ),* )
							}
						)*
					})
				}

				fn encode(&self) -> $crate::dispatch::Vec<u8> {
					let mut v = $crate::dispatch::Vec::new();
					match *self {
						$(
							Call::$fn_name(
								$(
									ref $param_name
								),*
							) => {
								(Id::$fn_name as u8).using_encoded(|s| v.extend(s));
								$(
									$param_name.using_encoded(|s| v.extend(s));
								)*
							}
						)*
					}
					v
				}

				fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
					f(self.encode().as_slice())
				}
			}
			impl $crate::dispatch::NonTrivialSlicable for Call {}
		}
	}
}

/// Implement a meta-dispatch module to dispatch to other dispatchers.
#[macro_export]
macro_rules! impl_meta_dispatch {
	(
		pub mod $super_name:ident;
		path $path:ident;
		trait $trait:ty;
		$(
			$camelcase:ident(mod $sub_name_head:ident $( :: $sub_name_tail:ident )* ) = $id:expr ;
		)*
	) => {
		pub mod $super_name {
			use super::*;

			#[derive(Clone, Copy, PartialEq, Eq)]
			#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
			#[repr(u32)]
			#[allow(non_camel_case_types)]
			enum Id {
				$(
					#[allow(non_camel_case_types)]
					$camelcase = $id,
				)*
			}

			impl Id {
				/// Derive `Some` value from a `u8`, or `None` if it's invalid.
				fn from_u8(value: u8) -> Option<Id> {
					match value {
						$(
							$id => Some(Id::$camelcase),
						)*
						_ => None,
					}
				}
			}

			#[derive(Clone, PartialEq, Eq)]
			#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
			#[allow(missing_docs)]
			pub enum Call {
				$(
					#[allow(non_camel_case_types)]
					$camelcase ( $sub_name_head $( :: $sub_name_tail )* ::$path::Call )
				,)*
			}

			impl Call {
				pub fn dispatch(self, d: $trait) {
					match self {
						$(
							Call::$camelcase(x) => x.dispatch(d),
						)*
					}
				}
			}

			impl $crate::dispatch::Slicable for Call {
				fn decode<I: $crate::dispatch::Input>(input: &mut I) -> Option<Self> {
					let id = u8::decode(input).and_then(Id::from_u8)?;
					Some(match id {
						$(
							Id::$camelcase =>
								Call::$camelcase( $crate::dispatch::Slicable::decode(input)? ),
						)*
					})
				}

				fn encode(&self) -> $crate::dispatch::Vec<u8> {
					let mut v = $crate::dispatch::Vec::new();
					match *self {
						$(
							Call::$camelcase( ref sub ) => {
								(Id::$camelcase as u8).using_encoded(|s| v.extend(s));
								sub.using_encoded(|s| v.extend(s));
							}
						)*
					}
					v
				}

				fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
					f(self.encode().as_slice())
				}
			}
			impl $crate::dispatch::NonTrivialSlicable for Call {}
		}
	}
}
