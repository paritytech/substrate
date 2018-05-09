// Copyright 2018 Parity Technologies (UK) Ltd.
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

use std::{
	sync::Weak,
	collections::HashMap,
};
use primitives::Hash;
use txpool;

use watcher::Watcher;

pub struct Listener<T> {
	_typ: ::std::marker::PhantomData<T>,
	watchers: HashMap<Hash, Weak<Watcher>>
}

impl<T> Default for Listener<T> {
	fn default() -> Self {
		Listener {
			_typ: Default::default(),
			watchers: Default::default(),
		}
	}
}

impl<T> txpool::Listener<T> for Listener<T> {

}


