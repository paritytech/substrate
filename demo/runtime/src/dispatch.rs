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

use demo_primitives::AccountId;
use runtime::{staking, system, session, democracy, council, council_vote};
use runtime::staking::public::Dispatch as staking_d;
use runtime::staking::privileged::Dispatch as staking_pd;
use runtime::timestamp::public::Dispatch as timestamp_d;

pub use rstd::prelude::Vec;
pub use codec::{Slicable, Input, NonTrivialSlicable};

#[macro_export]
macro_rules! impl_dispatch {
	(
		pub mod $mod_name:ident;
		$(
			fn $fn_name:ident(
				$(
					$param_name:ident : $param:ty
				),*
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
					use self::*;
					let functions = [
						$( Id::$fn_name ),*
					];
					functions.iter().map(|&f| f).find(|&f| value == f as u8)
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

				fn encode(&self) -> Vec<u8> {
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

macro_rules! impl_meta_dispatch {
	(
		pub mod $super_name:ident;
		path $path:ident;
		trait $trait:ty;
		$(
			$camelcase:ident(mod $sub_name:ident) = $id:expr ;
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
					use self::*;
					let functions = [
						$( Id::$camelcase ),*
					];
					functions.iter().map(|&f| f).find(|&f| value == f as u8)
				}
			}

			#[derive(Clone, PartialEq, Eq)]
			#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
			#[allow(missing_docs)]
			pub enum Call {
				$(
					#[allow(non_camel_case_types)]
					$camelcase ( $crate::runtime::$sub_name::$path::Call )
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

				fn encode(&self) -> Vec<u8> {
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

impl_meta_dispatch! {
	pub mod public;
	path public;
	trait staking::PublicPass;
	Staking(mod staking) = 0;
	Timestamp(mod timestamp) = 1;
	Democracy(mod democracy) = 5;
	Council(mod council) = 6;
	CouncilVote(mod council) = 7;
}

impl_meta_dispatch! {
	pub mod privileged;
	path privileged;
	trait system::PrivPass;
	Staking(mod staking) = 0;
	Democracy(mod democracy) = 5;
	Council(mod council) = 6;
	CouncilVote(mod council) = 7;
}

pub use self::privileged::Call as PrivCall;
pub use self::public::Call as PubCall;
