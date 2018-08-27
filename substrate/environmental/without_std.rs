// Copyright 2018 Parity Technologies (UK) Ltd.
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

#[doc(hidden)]
pub mod imp {
	pub use core::cell::RefCell;
	pub use core::mem::transmute;
	pub use core::mem::replace;

	// This code is a simplified version of [`LocalKey`] and it's wasm32 specialization: [`statik::Key`].
	// [`LocalKey`]: https://github.com/alexcrichton/rust/blob/98931165a23a1c2860d99759385f45d6807c8982/src/libstd/thread/local.rs#L89
	// [`statik::Key`]: https://github.com/alexcrichton/rust/blob/98931165a23a1c2860d99759385f45d6807c8982/src/libstd/thread/local.rs#L310-L312

	pub struct LocalKey<T: 'static> {
		pub init: fn() -> T,
		pub inner: RefCell<Option<T>>,
	}

	// This is safe as long there is no threads in wasm32.
	unsafe impl<T: 'static> ::core::marker::Sync for LocalKey<T> { }

	impl<T: 'static> LocalKey<T> {
		pub const fn new(init: fn() -> T) -> LocalKey<T> {
			LocalKey {
				init,
				inner: RefCell::new(None),
			}
		}

		pub fn with<F, R>(&'static self, f: F) -> R
		where F: FnOnce(&T) -> R
		{
			if self.inner.borrow().is_none() {
				let v = (self.init)();
				*self.inner.borrow_mut() = Some(v);
			}
			// This code can't panic because:
			// 1. `inner` can be borrowed mutably only once at the initialization time.
			// 2. After the initialization `inner` is always `Some`.
			f(&*self.inner.borrow().as_ref().unwrap())
		}
	}
}

#[doc(hidden)]
#[macro_export]
macro_rules! thread_local_impl {
	($(#[$attr:meta])* static $name:ident: $t:ty = $init:expr) => (
		$(#[$attr])*
		static $name: $crate::imp::LocalKey<$t> = {
			fn __init() -> $t { $init }

			$crate::imp::LocalKey::new(__init)
		};
	);
}
