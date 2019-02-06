// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Support code for the runtime.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]

#[cfg(feature = "std")]
pub use serde;
#[doc(hidden)]
pub use sr_std as rstd;
#[doc(hidden)]
pub use parity_codec as codec;
#[doc(hidden)]
pub use parity_codec_derive;
#[cfg(feature = "std")]
#[doc(hidden)]
pub use once_cell;
#[doc(hidden)]
pub use paste;
pub use sr_primitives as runtime_primitives;

pub use self::storage::generator::Storage as GenericStorage;

#[macro_use]
pub mod dispatch;
#[macro_use]
pub mod storage;
mod hashable;
#[macro_use]
pub mod event;
#[macro_use]
mod origin;
#[macro_use]
pub mod metadata;
#[macro_use]
mod runtime;
#[macro_use]
pub mod inherent;
mod double_map;

pub use self::storage::{StorageVec, StorageList, StorageValue, StorageMap};
pub use self::hashable::Hashable;
pub use self::dispatch::{Parameter, Dispatchable, Callable, IsSubType};
pub use runtime_io::print;
pub use double_map::StorageDoubleMap;

#[doc(inline)]
pub use srml_support_procedural::decl_storage;

#[macro_export]
macro_rules! fail {
	( $y:expr ) => {{
		return Err($y);
	}}
}

#[macro_export]
macro_rules! ensure {
	( $x:expr, $y:expr ) => {{
		if !$x {
			fail!($y);
		}
	}}
}

#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_noop {
	( $x:expr , $y:expr ) => {
		let h = runtime_io::storage_root();
		assert_err!($x, $y);
		assert_eq!(h, runtime_io::storage_root());
	}
}

#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_err {
	( $x:expr , $y:expr ) => {
		assert_eq!($x, Err($y));
	}
}

#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_ok {
	( $x:expr ) => {
		assert_eq!($x, Ok(()));
	};
	( $x:expr, $y:expr ) => {
		assert_eq!($x, Ok($y));
	}
}

/// The void type - it cannot exist.
// Oh rust, you crack me up...
#[derive(Clone, Eq, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Void {}

#[cfg(feature = "std")]
#[doc(hidden)]
pub use serde_derive::*;

/// Programatically create derivations for tuples of up to 19 elements. You provide a second macro
/// which is called once per tuple size, along with a number of identifiers, one for each element
/// of the tuple.
#[macro_export]
macro_rules! for_each_tuple {
	($m:ident) => {
		for_each_tuple! { @IMPL $m !! A, B, C, D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, }
	};
	(@IMPL $m:ident !!) => { $m! { } };
	(@IMPL $m:ident !! $h:ident, $($t:ident,)*) => {
		$m! { $h $($t)* }
		for_each_tuple! { @IMPL $m !! $($t,)* }
	}
}
