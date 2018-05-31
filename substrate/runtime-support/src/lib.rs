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

//! Support code for the runtime.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
extern crate serde;

#[cfg(feature = "std")]
#[allow(unused_imports)] // can be removed when fixed: https://github.com/rust-lang/rust/issues/43497
#[macro_use]
extern crate serde_derive;

#[cfg(feature = "std")]
pub use serde_derive::*;

extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_primitives as primitives;

#[doc(hidden)]
pub extern crate substrate_codec as codec;
pub use self::storage::generator::Storage as GenericStorage;

pub mod dispatch;
pub mod storage;
mod hashable;

pub use self::storage::{StorageVec, StorageList, StorageValue, StorageMap};
pub use self::hashable::Hashable;
pub use self::dispatch::{Parameter, Dispatchable, Callable, AuxDispatchable, AuxCallable, IsSubType, IsAuxSubType};
pub use runtime_io::print;

#[macro_export]
macro_rules! fail {
	( $y:expr ) => {{
		$crate::print($y);
		return;
	}}
}

#[macro_export]
macro_rules! ensure {
	( $x:expr, $y:expr ) => {{
		if !$x {
			fail!($y);
		}
	}};
	($x:expr) => {{
		if !$x {
			$crate::print("Bailing! Cannot ensure: ");
			$crate::print(stringify!($x));
			return;
		}
	}}
}

#[macro_export]
macro_rules! ensure_unwrap {
	($x:expr, $y: expr) => {
		if let Some(v) = $x {
			v
		} else {
			fail!{$y}
		}
	}
}

#[macro_export]
macro_rules! ensure_unwrap_err {
	($x:expr, $y: expr) => {
		if let Err(v) = $x {
			v
		} else {
			fail!{$y}
		}
	}
}

#[macro_export]
#[cfg(feature = "std")]
macro_rules! assert_noop {
	( $( $x:tt )* ) => {
		let h = runtime_io::storage_root();
		{
			$( $x )*
		}
		assert_eq!(h, runtime_io::storage_root());
	}
}
