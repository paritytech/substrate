// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

use frame_support::codec::{Encode, Decode, EncodeLike};

pub trait Trait: 'static + Eq + Clone {
	type Origin: Into<Result<RawOrigin<Self::AccountId>, Self::Origin>>
		+ From<RawOrigin<Self::AccountId>>;

	type BaseCallFilter: frame_support::traits::Filter<Self::Call>;
	type BlockNumber: Decode + Encode + EncodeLike + Clone + Default;
	type Hash;
	type AccountId: Encode + EncodeLike + Decode;
	type Call;
	type Event: From<Event<Self>>;
	type ModuleToIndex: frame_support::traits::ModuleToIndex;
}

frame_support::decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
}

impl<T: Trait> Module<T> {
	pub fn deposit_event(_event: impl Into<T::Event>) {}
}

frame_support::decl_event!(
	pub enum Event<T> where BlockNumber = <T as Trait>::BlockNumber {
		ExtrinsicSuccess,
		ExtrinsicFailed,
		Ignore(BlockNumber),
	}
);

frame_support::decl_error! {
	pub enum Error for Module<T: Trait> {
		/// Test error documentation
		TestError,
		/// Error documentation
		/// with multiple lines
		AnotherError
	}
}

/// Origin for the system module.
#[derive(PartialEq, Eq, Clone, sp_runtime::RuntimeDebug)]
pub enum RawOrigin<AccountId> {
	Root,
	Signed(AccountId),
	None,
}

impl<AccountId> From<Option<AccountId>> for RawOrigin<AccountId> {
	fn from(s: Option<AccountId>) -> RawOrigin<AccountId> {
		match s {
			Some(who) => RawOrigin::Signed(who),
			None => RawOrigin::None,
		}
	}
}

pub type Origin<T> = RawOrigin<<T as Trait>::AccountId>;

#[allow(dead_code)]
pub fn ensure_root<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<(), &'static str>
	where OuterOrigin: Into<Result<RawOrigin<AccountId>, OuterOrigin>>
{
	o.into().map(|_| ()).map_err(|_| "bad origin: expected to be a root origin")
}
