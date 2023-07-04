// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use crate::{
	dispatch::{CallMetadata, DispatchInfo, DispatchResultWithPostInfo, PostDispatchInfo},
	traits::{EnqueueMessage, GetCallMetadata, UnfilteredDispatchable},
};
use codec::{Codec, Decode, Encode, Error, Input, MaxEncodedLen, Output};
use frame_support::dispatch::DispatchErrorWithPostInfo;
use frame_support::Parameter;
use scale_info::{Type, TypeInfo};
use sp_core::{RuntimeDebug, H256};
use sp_runtime::traits::Member;
use sp_runtime::{
	traits,
	traits::{Dispatchable, Zero},
	DispatchError, DispatchResultWithInfo, ModuleError, MAX_MODULE_ERROR_ENCODED_SIZE,
};
use sp_std::fmt::Debug;
use sp_std::marker::PhantomData;
use std::fmt::Formatter;

/// Runtime API that provides view access
sp_api::decl_runtime_apis! {
	pub trait Interface<View>
		where View: sp_api::Encode + frame_support::interface::View
	{
		fn view(view: View) -> ViewResult<Vec<u8>>;
	}
}

/// The result a call method of an interface must have
pub type CallResult = Result<PostDispatchInfo, DispatchErrorWithPostInfo>;

/// The result a view method of an interface must have
pub type ViewResult<T> = Result<T, DispatchErrorWithPostInfo>;

/// The result a selector method of an interface must have
pub type SelectorResult<T> = Result<SelectorResultWithInfo<T>, DispatchErrorWithPostInfo>;

/// A helper struct that provides easy conversions
///
/// I.e. it allows somebody who does not care about
///      the `PostDispatchInfo` in a selector method
///      to just call `Ok(T.into())` instead of
///      Ok((T, ().into())) if we used a tuple.
pub struct SelectorResultWithInfo<T> {
	res: T,
	info: PostDispatchInfo,
}

impl<T> From<T> for SelectorResultWithInfo<T> {
	fn from(value: T) -> Self {
		SelectorResultWithInfo { res: value, info: Default::default() }
	}
}

impl<T> From<(T, PostDispatchInfo)> for SelectorResultWithInfo<T> {
	fn from(value: (T, PostDispatchInfo)) -> Self {
		SelectorResultWithInfo { res: value.0, info: value.1 }
	}
}

impl<T> SelectorResultWithInfo<T> {
	/// Consumes self and returns the
	/// inner T
	pub fn result(self) -> T {
		self.res
	}

	/// Provides a copy of the inner
	/// `PostDispatchInfo`
	pub fn info(&self) -> PostDispatchInfo {
		self.info
	}

	/// Destructs self into a tuple of `(T, PostDispatchInfo)`
	pub fn destruct(self) -> (T, PostDispatchInfo) {
		(self.res, self.info)
	}
}

pub trait View {
	fn view(self) -> ViewResult<Vec<u8>>;
}

pub trait Selector {
	type Selectable: Parameter + Member + MaxEncodedLen;
	type Selected;

	fn select(selectable: Self::Selectable) -> SelectorResult<Self::Selected>;
}

pub struct Select<T: Selector> {
	from: T::Selectable,
	_phantom: PhantomData<T>,
}

impl<T: Selector> Debug for Select<T> {
	fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
		self.from.fmt(f)
	}
}

impl<T: Selector> Clone for Select<T> {
	fn clone(&self) -> Self {
		Select { from: self.from.clone(), _phantom: Default::default() }
	}
}

impl<T: Selector> Encode for Select<T> {
	fn size_hint(&self) -> usize {
		self.from.size_hint()
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		self.from.using_encoded(f)
	}

	fn encode(&self) -> Vec<u8> {
		self.from.encode()
	}

	fn encode_to<O: Output + ?Sized>(&self, dest: &mut O) {
		self.from.encode_to(dest)
	}

	fn encoded_size(&self) -> usize {
		self.from.encoded_size()
	}
}

impl<T: Selector> Decode for Select<T> {
	fn decode<I: Input>(input: &mut I) -> Result<Self, Error> {
		let from: T::Selectable = Decode::decode(input)?;

		Ok(Select { from, _phantom: Default::default() })
	}
}

impl<T: Selector> MaxEncodedLen for Select<T> {
	fn max_encoded_len() -> usize {
		T::Selectable::max_encoded_len()
	}
}

impl<T: Selector> PartialEq for Select<T> {
	fn eq(&self, other: &Self) -> bool {
		self.from == other.from
	}
}

impl<T: Selector> Eq for Select<T> {}

impl<T: Selector> TypeInfo for Select<T> {
	type Identity = T::Selectable;

	fn type_info() -> Type {
		T::Selectable::type_info()
	}
}

impl<T: Selector> Select<T> {
	pub fn select(self) -> SelectorResult<T::Selected> {
		T::select(self.from)
	}
}
