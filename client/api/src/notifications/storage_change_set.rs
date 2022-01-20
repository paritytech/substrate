// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use super::*;

/// Storage change set
#[derive(Debug)]
pub struct StorageChangeSet {
	pub(super) changes: Arc<[(StorageKey, Option<StorageData>)]>,
	pub(super) child_changes: Arc<[(StorageKey, Vec<(StorageKey, Option<StorageData>)>)]>,
	pub(super) filter: Keys,
	pub(super) child_filters: ChildKeys,
}

impl StorageChangeSet {
	/// Convert the change set into iterator over storage items.
	pub fn iter<'a>(
		&'a self,
	) -> impl Iterator<Item = (Option<&'a StorageKey>, &'a StorageKey, Option<&'a StorageData>)> + 'a
	{
		let top = self
			.changes
			.iter()
			.filter(move |&(key, _)| match self.filter {
				Some(ref filter) => filter.contains(key),
				None => true,
			})
			.map(move |(k, v)| (None, k, v.as_ref()));
		let children = self
			.child_changes
			.iter()
			.filter_map(move |(sk, changes)| {
				self.child_filters.as_ref().and_then(|cf| {
					cf.get(sk).map(|filter| {
						changes
							.iter()
							.filter(move |&(key, _)| match filter {
								Some(ref filter) => filter.contains(key),
								None => true,
							})
							.map(move |(k, v)| (Some(sk), k, v.as_ref()))
					})
				})
			})
			.flatten();
		top.chain(children)
	}
}
