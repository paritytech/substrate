// Copyright 2017 Parity Technologies (UK) Ltd.
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

#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(feature = "std")]
extern crate serde;

extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_primitives as primitives;

#[cfg(test)]
#[macro_use]
extern crate pretty_assertions;
#[cfg(test)]
#[macro_use]
extern crate serde_derive;
#[cfg(test)]
extern crate serde_json;
#[cfg(test)]
#[macro_use]
extern crate substrate_codec_derive;

#[doc(hidden)]
pub extern crate substrate_codec as codec;
pub use self::storage::generator::Storage as GenericStorage;

#[cfg(feature = "std")]
pub mod alloc {
	pub use std::boxed;
	pub use std::vec;
}

#[macro_use]
pub mod dispatch;
#[macro_use]
pub mod storage;
mod hashable;
#[macro_use]
mod event;
#[macro_use]
pub mod metadata;

pub use self::storage::{StorageVec, StorageList, StorageValue, StorageMap};
pub use self::hashable::Hashable;
pub use self::dispatch::{Parameter, Dispatchable, Callable, IsSubType};
pub use runtime_io::print;


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

#[macro_export]
macro_rules! impl_outer_origin {
	($(#[$attr:meta])* pub enum $name:ident for $trait:ident where system = $system:ident { $( $module:ident ),* }) => {
		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug))]
		$(#[$attr])*
		#[allow(non_camel_case_types)]
		pub enum $name {
			system($system::Origin<$trait>),
			$(
				$module($module::Origin),
			)*
			#[allow(dead_code)]
			Void($crate::Void)
		}
		#[allow(dead_code)]
		impl $name {
			pub const INHERENT: Self = $name::system($system::RawOrigin::Inherent);
			pub const ROOT: Self = $name::system($system::RawOrigin::Root);
			pub fn signed(by: <$trait as $system::Trait>::AccountId) -> Self {
				$name::system($system::RawOrigin::Signed(by))
			}
		}
		impl From<$system::Origin<$trait>> for $name {
			fn from(x: $system::Origin<$trait>) -> Self {
				$name::system(x)
			}
		}
		impl Into<Option<$system::Origin<$trait>>> for $name {
			fn into(self) -> Option<$system::Origin<$trait>> {
				if let $name::system(l) = self {
					Some(l)
				} else {
					None
				}
			}
		}
		impl From<Option<<$trait as $system::Trait>::AccountId>> for $name {
			fn from(x: Option<<$trait as $system::Trait>::AccountId>) -> Self {
				<$system::Origin<$trait>>::from(x).into()
			}
		}
		$(
			impl From<$module::Origin> for $name {
				fn from(x: $module::Origin) -> Self {
					$name::$module(x)
				}
			}
			impl Into<Option<$module::Origin>> for $name {
				fn into(self) -> Option<$module::Origin> {
					if let $name::$module(l) = self {
						Some(l)
					} else {
						None
					}
				}
			}
		)*
	};
	($(#[$attr:meta])* pub enum $name:ident for $trait:ident { $( $module:ident ),* }) => {
		impl_outer_origin! {
			$(#[$attr])*
			pub enum $name for $trait where system = system {
				$( $module ),*
			}
		}
	}
}
