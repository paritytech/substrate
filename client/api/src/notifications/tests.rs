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

use sp_runtime::testing::{Block as RawBlock, ExtrinsicWrapper, H256 as Hash};
use std::iter::{empty, Empty};

type TestChangeSet = (
	Vec<(StorageKey, Option<StorageData>)>,
	Vec<(StorageKey, Vec<(StorageKey, Option<StorageData>)>)>,
);

impl From<TestChangeSet> for StorageChangeSet {
	fn from(changes: TestChangeSet) -> Self {
		// warning hardcoded child trie wildcard to test upon
		let child_filters = Some(
			[(StorageKey(vec![4]), None), (StorageKey(vec![5]), None)]
				.iter()
				.cloned()
				.collect(),
		);
		StorageChangeSet {
			changes: From::from(changes.0),
			child_changes: From::from(changes.1),
			filter: None,
			child_filters,
		}
	}
}

impl PartialEq for StorageChangeSet {
	fn eq(&self, other: &Self) -> bool {
		self.iter().eq(other.iter())
	}
}

type Block = RawBlock<ExtrinsicWrapper<Hash>>;

#[test]
fn triggering_change_should_notify_wildcard_listeners() {
	// given
	let notifications = StorageNotifications::<Block>::new(None);
	let child_filter = [(StorageKey(vec![4]), None)];
	let mut recv =
		futures::executor::block_on_stream(notifications.listen(None, Some(&child_filter[..])));

	// when
	let changeset = vec![(vec![2], Some(vec![3])), (vec![3], None)];
	let c_changeset_1 = vec![(vec![5], Some(vec![4])), (vec![6], None)];
	let c_changeset = vec![(vec![4], c_changeset_1)];
	notifications.trigger(
		&Hash::from_low_u64_be(1),
		changeset.into_iter(),
		c_changeset.into_iter().map(|(a, b)| (a, b.into_iter())),
	);

	// then
	assert_eq!(
		recv.next().map(StorageNotification::into_fields).unwrap(),
		(
			Hash::from_low_u64_be(1),
			(
				vec![
					(StorageKey(vec![2]), Some(StorageData(vec![3]))),
					(StorageKey(vec![3]), None),
				],
				vec![(
					StorageKey(vec![4]),
					vec![
						(StorageKey(vec![5]), Some(StorageData(vec![4]))),
						(StorageKey(vec![6]), None),
					]
				)]
			)
				.into()
		)
	);
}

#[test]
fn should_only_notify_interested_listeners() {
	// given
	let notifications = StorageNotifications::<Block>::new(None);
	let child_filter = [(StorageKey(vec![4]), Some(vec![StorageKey(vec![5])]))];
	let mut recv1 = futures::executor::block_on_stream(
		notifications.listen(Some(&[StorageKey(vec![1])]), None),
	);
	let mut recv2 = futures::executor::block_on_stream(
		notifications.listen(Some(&[StorageKey(vec![2])]), None),
	);
	let mut recv3 =
		futures::executor::block_on_stream(notifications.listen(Some(&[]), Some(&child_filter)));

	// when
	let changeset = vec![(vec![2], Some(vec![3])), (vec![1], None)];
	let c_changeset_1 = vec![(vec![5], Some(vec![4])), (vec![6], None)];

	let c_changeset = vec![(vec![4], c_changeset_1)];
	notifications.trigger(
		&Hash::from_low_u64_be(1),
		changeset.into_iter(),
		c_changeset.into_iter().map(|(a, b)| (a, b.into_iter())),
	);

	// then
	assert_eq!(
		recv1.next().map(StorageNotification::into_fields).unwrap(),
		(Hash::from_low_u64_be(1), (vec![(StorageKey(vec![1]), None),], vec![]).into())
	);
	assert_eq!(
		recv2.next().map(StorageNotification::into_fields).unwrap(),
		(
			Hash::from_low_u64_be(1),
			(vec![(StorageKey(vec![2]), Some(StorageData(vec![3]))),], vec![]).into()
		)
	);
	assert_eq!(
		recv3.next().map(StorageNotification::into_fields).unwrap(),
		(
			Hash::from_low_u64_be(1),
			(
				vec![],
				vec![(
					StorageKey(vec![4]),
					vec![(StorageKey(vec![5]), Some(StorageData(vec![4])))]
				),]
			)
				.into()
		)
	);
}

#[test]
fn should_cleanup_subscribers_if_dropped() {
	// given
	let notifications = StorageNotifications::<Block>::new(None);
	{
		let child_filter = [(StorageKey(vec![4]), Some(vec![StorageKey(vec![5])]))];
		let _recv1 = futures::executor::block_on_stream(
			notifications.listen(Some(&[StorageKey(vec![1])]), None),
		);
		let _recv2 = futures::executor::block_on_stream(
			notifications.listen(Some(&[StorageKey(vec![2])]), None),
		);
		let _recv3 = futures::executor::block_on_stream(notifications.listen(None, None));
		let _recv4 =
			futures::executor::block_on_stream(notifications.listen(None, Some(&child_filter)));
		assert_eq!(notifications.map_registry(|r| r.listeners.len()), 2);
		assert_eq!(notifications.map_registry(|r| r.wildcard_listeners.len()), 2);
		assert_eq!(notifications.map_registry(|r| r.child_listeners.len()), 1);
	}

	// when
	let changeset = vec![(vec![2], Some(vec![3])), (vec![1], None)];
	let c_changeset = empty::<(_, Empty<_>)>();
	notifications.trigger(&Hash::from_low_u64_be(1), changeset.into_iter(), c_changeset);

	// then
	assert_eq!(notifications.map_registry(|r| r.listeners.len()), 0);
	assert_eq!(notifications.map_registry(|r| r.wildcard_listeners.len()), 0);
	assert_eq!(notifications.map_registry(|r| r.child_listeners.len()), 0);
}

#[test]
fn should_cleanup_subscriber_if_stream_is_dropped() {
	let notifications = StorageNotifications::<Block>::new(None);
	let stream = notifications.listen(None, None);
	assert_eq!(notifications.map_registry(|r| r.sinks.len()), 1);
	std::mem::drop(stream);
	assert_eq!(notifications.map_registry(|r| r.sinks.len()), 0);
}

#[test]
fn should_not_send_empty_notifications() {
	// given
	let mut recv = {
		let notifications = StorageNotifications::<Block>::new(None);
		let recv = futures::executor::block_on_stream(notifications.listen(None, None));

		// when
		let changeset = vec![];
		let c_changeset = empty::<(_, Empty<_>)>();
		notifications.trigger(&Hash::from_low_u64_be(1), changeset.into_iter(), c_changeset);
		recv
	};

	// then
	assert_eq!(recv.next().map(StorageNotification::into_fields), None);
}

impl<B: BlockT> StorageNotifications<B> {
	fn map_registry<MapF, Ret>(&self, map: MapF) -> Ret
	where
		MapF: FnOnce(&Registry) -> Ret,
	{
		self.0.map_registry_for_tests(map)
	}
}

impl<H> StorageNotification<H> {
	fn into_fields(self) -> (H, StorageChangeSet) {
		let Self { block, changes } = self;
		(block, changes)
	}
}
