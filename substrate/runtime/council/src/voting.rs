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

//! Council voting system.

use rstd::prelude::*;
use rstd::cmp;
use rstd::marker::PhantomData;
use integer_sqrt::IntegerSquareRoot;
//use runtime_io::{twox_128, TestExternalities};
use primitives::{Zero, One, Bounded, SimpleArithmetic, Executable};
use runtime_support::{StorageValue, StorageMap, Parameter};

pub trait Trait: super::Trait {
}

decl_module! {
	pub struct Module<T: Trait>;
	pub enum Call where aux: T::PublicAux {
	}
	pub enum PrivCall {
	}
}

decl_storage! {
	trait Store for Module<T: Trait>;
}

impl<T: Trait> Module<T> {
}

impl<T: Trait> Executable for Module<T> {
	fn execute() {
	}
}
