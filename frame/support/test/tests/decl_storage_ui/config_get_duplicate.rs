// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

pub trait Trait {
	type Origin;
	type BlockNumber: codec::Codec + codec::EncodeLike + Default + Clone;
}

frame_support::decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
}

frame_support::decl_storage!{
	trait Store for Module<T: Trait> as FinalKeysNone {
		pub Value get(fn value) config(): u32;
		pub Value2 config(value): u32;
	}
}

fn main() {}
