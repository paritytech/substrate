// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Update `CodeStorage` with the new `determinism` field.

use crate::{
	migration::{IsFinished, Migrate},
	Config, Weight,
};
use codec::{Decode, Encode};
use frame_support::{codec, pallet_prelude::*, DefaultNoBound};
use sp_std::marker::PhantomData;

#[derive(Encode, Decode, MaxEncodedLen, DefaultNoBound)]
pub struct Migration<T: Config> {
	_phantom: PhantomData<T>,
}

impl<T: Config> Migrate for Migration<T> {
	const VERSION: u16 = 10;

	fn max_step_weight() -> Weight {
		Weight::zero() // TODO fix
	}

	fn step(&mut self) -> (IsFinished, Weight) {
		// TODO
		(IsFinished::Yes, Self::max_step_weight())
	}
}
