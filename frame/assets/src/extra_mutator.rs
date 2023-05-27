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

//! Datatype for easy mutation of the extra "sidecar" data.

use super::*;

/// A mutator type allowing inspection and possible modification of the extra "sidecar" data.
///
/// This may be used as a `Deref` for the pallet's extra data. If mutated (using `DerefMut`), then
/// any uncommitted changes (see `commit` function) will be automatically committed to storage when
/// dropped. Changes, even after committed, may be reverted to their original values with the
/// `revert` function.
pub struct ExtraMutator<T: Config<I>, I: 'static = ()> {
	id: T::AssetId,
	who: T::AccountId,
	original: T::Extra,
	pending: Option<T::Extra>,
}

impl<T: Config<I>, I: 'static> Drop for ExtraMutator<T, I> {
	fn drop(&mut self) {
		debug_assert!(self.commit().is_ok(), "attempt to write to non-existent asset account");
	}
}

impl<T: Config<I>, I: 'static> sp_std::ops::Deref for ExtraMutator<T, I> {
	type Target = T::Extra;
	fn deref(&self) -> &T::Extra {
		match self.pending {
			Some(ref value) => value,
			None => &self.original,
		}
	}
}

impl<T: Config<I>, I: 'static> sp_std::ops::DerefMut for ExtraMutator<T, I> {
	fn deref_mut(&mut self) -> &mut T::Extra {
		if self.pending.is_none() {
			self.pending = Some(self.original.clone());
		}
		self.pending.as_mut().unwrap()
	}
}

impl<T: Config<I>, I: 'static> ExtraMutator<T, I> {
	pub(super) fn maybe_new(
		id: T::AssetId,
		who: impl sp_std::borrow::Borrow<T::AccountId>,
	) -> Option<ExtraMutator<T, I>> {
		if let Some(a) = Account::<T, I>::get(&id, who.borrow()) {
			Some(ExtraMutator::<T, I> {
				id,
				who: who.borrow().clone(),
				original: a.extra,
				pending: None,
			})
		} else {
			None
		}
	}

	/// Commit any changes to storage.
	pub fn commit(&mut self) -> Result<(), ()> {
		if let Some(extra) = self.pending.take() {
			Account::<T, I>::try_mutate(&self.id, &self.who, |maybe_account| {
				maybe_account.as_mut().ok_or(()).map(|account| account.extra = extra)
			})
		} else {
			Ok(())
		}
	}

	/// Revert any changes, even those already committed by `self` and drop self.
	pub fn revert(mut self) -> Result<(), ()> {
		self.pending = None;
		Account::<T, I>::try_mutate(&self.id, &self.who, |maybe_account| {
			maybe_account
				.as_mut()
				.ok_or(())
				.map(|account| account.extra = self.original.clone())
		})
	}
}
