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

//! Democracy.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")] extern crate serde;

extern crate substrate_codec as codec;
extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_io as runtime_io;
#[macro_use] extern crate substrate_runtime_support as runtime_support;
extern crate substrate_runtime_primitives as primitives;
extern crate substrate_runtime_session as session;
extern crate substrate_runtime_staking as staking;
extern crate substrate_runtime_system as system;

use rstd::prelude::*;
use rstd::cmp;
use rstd::marker::PhantomData;
//use runtime_io::{twox_128, TestExternalities};
use primitives::{Zero, One, Bounded, SimpleArithmetic, Executable};
use runtime_support::{StorageValue, StorageMap, Parameter};

mod vote_threshold;
pub use vote_threshold::VoteThreshold;

/// A proposal index.
pub type PropIndex = u32;
/// A referendum index.
pub type ReferendumIndex = u32;

pub trait Trait: staking::Trait {
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
