// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Test utilities

use super::*;

use frame_support::{
	impl_outer_origin, impl_outer_dispatch, impl_outer_event, parameter_types,
	weights::Weight,
	traits::{OnInitialize, OnFinalize},
};
use sp_core::H256;
// The testing primitives are very useful for avoiding having to work with signatures
// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
use sp_runtime::{
	Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header,
};
use crate as sudo;

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

// For testing the pallet, we construct most of a mock runtime. This means
// first constructing a configuration type (`Test`) which `impl`s each of the
// configuration traits of pallets we want to use.
#[derive(Clone, Eq, PartialEq)]
pub struct Test;

impl frame_system::Trait for Test {
	type Event = ();
	type Call = ();
}


// impl Trait for TestRuntime {
//     type Event = ();
// }

pub type Sudo = Module<Test>;
pub type System = frame_system::Module<Test>;
