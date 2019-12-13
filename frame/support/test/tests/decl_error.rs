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

// Test decl_error using impl_from_frame_system works
#[cfg(test)]
mod tests {
	// No doc but impl_from_frame_system
	support::decl_error!(
		#[substrate(impl_from_frame_system(frame_system))]
		pub enum Error1 {
			MyError,
		}
	);

	// Doc and impl_from_frame_system
	support::decl_error!(
		/// Doc
		#[substrate(impl_from_frame_system(frame_system))]
		/// Doc
		pub enum Error2 {
			MyError,
		}
	);

	// No doc no impl_from_frame_system
	support::decl_error!(
		pub enum Error3 {
			MyError,
		}
	);

	// Doc but no impl_from_frame_system
	support::decl_error!(
		/// Doc
		pub enum Error4 {
			MyError,
		}
	);


	#[test]
	fn works() {
		fn assert_impl_from_frame_system<T: From<frame_system::Error>>() {};

		assert_impl_from_frame_system::<Error1>();
		assert_impl_from_frame_system::<Error2>();
	}
}
