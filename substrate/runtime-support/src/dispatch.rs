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
pub use rstd::marker::PhantomData;
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

/*
impl_dispatch! {
	trait Trait as T;
	pub mod public for Module;
	aux T::PublicAux;
	fn set(_, now: T::Timestamp) = 0;
}
*/

pub trait Dispatchable {
	type AuxType;
	type TraitType;
	fn dispatch(self, aux: &Self::AuxType);
}

/// Declare a struct for this module, then implement dispatch logic to create a pairing of several
/// dispatch traits and enums.
#[macro_export]
macro_rules! decl_module {
	(
		trait $trait_name:ident as $trait_instance:ident;
		struct $mod_type:ident;
		$($rest:tt)*
	) => {
		pub struct $mod_type<$trait_instance: $trait_name>($crate::dispatch::PhantomData<$trait_instance>);
		decl_dispatch! {
			trait $trait_name as $trait_instance;
			struct $mod_type;
			$($rest)*
		}
	}
}

/// Implement several dispatch modules to create a pairing of a dispatch trait and enum.
#[macro_export]
macro_rules! decl_dispatch {
	(
		trait $trait_name:ident as $trait_instance:ident;
		struct $mod_type:ident;
		pub mod $mod_name:ident aux $aux_type:ty {
			$(
				fn $fn_name:ident(_
					$(
						, $param_name:ident : $param:ty
					)*
				)
				= $id:expr ;
			)*
		}
		$($rest:tt)*
	) => {
		__decl_dispatch_module! {
			trait $trait_name as $trait_instance;
			pub mod $mod_name for $mod_type;
			aux $aux_type;
			$(
				fn $fn_name(_, $($param_name: $param),*)= $id;
			)*
		}
		decl_dispatch! {
			trait $trait_name as $trait_instance;
			struct $mod_type;
			$($rest)*
		}
	};
	(
		trait $trait_name:ident as $trait_instance:ident;
		struct $mod_type:ident;
	) => {
		impl<$trait_instance: $trait_name> $mod_type<$trait_instance> {
			pub fn dispatch<D: $crate::dispatch::Dispatchable<TraitType = $trait_instance>>(d: D, aux: &D::AuxType) {
				d.dispatch(aux);
			}
		}
	}
}

#[macro_export]
macro_rules! __decl_dispatch_fns {
	($aux_type:ty => $fn_name:ident ( $( $param_name:ident $param_type:ty )* ) $($rest:tt)*) => {
		fn $fn_name (aux: &$aux_type, $( $param_name: $param_type ),* );
		__decl_dispatch_fns!($aux_type => $($rest)*);
	};
	($aux_type:ty =>) => ()
}

#[macro_export]
/// Implement a single dispatch modules to create a pairing of a dispatch trait and enum.
macro_rules! __decl_dispatch_module {
	(
		trait $trait_name:ident as $trait_instance:ident;
		pub mod $mod_name:ident for $mod_type:ident;
		aux $aux_type:ty;

		$(
			fn $fn_name:ident(_
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
			#[cfg_attr(feature = "std", derive(Serialize, Debug))]
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
			#[cfg_attr(feature = "std", derive(Serialize, Debug))]
			#[allow(missing_docs)]
			pub enum Call<$trait_instance: $trait_name> {
				$(
					#[allow(non_camel_case_types)]
					$fn_name ( $( $param ),* )
				,)*
				__PhantomItem($crate::dispatch::PhantomData<$trait_instance>),
			}
			//pub enum Callable<T: Trait> { set(T::Timestamp) }

			pub trait Dispatch<$trait_instance: $trait_name>: Sized {
				__decl_dispatch_fns!{ $aux_type => $( $fn_name ( $( $param_name $param )* ) )* }
			}
			//pub trait Dispatch<T: Trait> { fn set(aux: &T::PublicAux, now: T::Timestamp); }

			impl<$trait_instance: $trait_name> $crate::dispatch::Dispatchable
				for Call<$trait_instance>
				where $mod_type<$trait_instance>: Dispatch<$trait_instance>
			//impl<T: Trait> super::Dispatchable for Callable<T> where super::Module<T>: Dispatch<T> {
			{
				type TraitType = $trait_instance;
				type AuxType = $aux_type;
				//type TraitType = T;
				//type AuxType = T::PublicAux;
				fn dispatch(self, aux: &Self::AuxType) {
				//fn dispatch(self, aux: &Self::AuxType) {
					match self {
						$(
							Call::$fn_name( $( $param_name ),* ) =>
								<$mod_type<$trait_instance>>::$fn_name( aux, $( $param_name ),* ),
							//Callable::set(a) => <super::Module<T>>::set(aux, a),
							Call::__PhantomItem(_) => unreachable!(),
						)*
					}
				}
			}

			impl<$trait_instance: $trait_name> $crate::dispatch::Slicable for Call<$trait_instance> {
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
						Call::__PhantomItem(_) => unreachable!(),
					}
					v
				}

				fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
					f(self.encode().as_slice())
				}
			}
			impl<$trait_instance: $trait_name> $crate::dispatch::NonTrivialSlicable for Call<$trait_instance> {}
		}
	}
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
