// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use std::panic::{catch_unwind, AssertUnwindSafe};

fn assert_hub_props(hub: &TestHub, sinks_count: usize, subs_count: usize) {
	assert_eq!(hub.sink_count(), sinks_count);
	assert_eq!(hub.subs_count(), subs_count);
}

#[test]
fn t01() {
	let hub = TestHub::new(TK);
	assert_hub_props(&hub, 0, 0);

	let rx_01 = hub.subscribe(SubsKey::new());
	assert_hub_props(&hub, 1, 1);

	std::mem::drop(rx_01);
	assert_hub_props(&hub, 0, 0);
}

#[test]
fn t02() {
	block_on(async {
		// Create a Hub
		let hub = TestHub::new(TK);
		assert_hub_props(&hub, 0, 0);

		// Subscribe rx-01
		let rx_01 = hub.subscribe(SubsKey::new());
		assert_hub_props(&hub, 1, 1);

		// Subscribe rx-02 so that its unsubscription will lead to an attempt to drop rx-01 in the
		// middle of unsubscription of rx-02
		let rx_02 = hub.subscribe(SubsKey::new().with_receiver(rx_01));
		assert_hub_props(&hub, 2, 2);

		// Subscribe rx-03 in order to see that it will receive messages after the unclean
		// unsubscription
		let mut rx_03 = hub.subscribe(SubsKey::new());
		assert_hub_props(&hub, 3, 3);

		// drop rx-02 leads to an attempt to unsubscribe rx-01
		assert!(catch_unwind(AssertUnwindSafe(move || {
			std::mem::drop(rx_02);
		}))
		.is_err());

		// One of the rxes could not unsubscribe
		assert_hub_props(&hub, 2, 2);

		// Subscribe rx-04 in order to see that it will receive messages after the unclean
		// unsubscription
		let mut rx_04 = hub.subscribe(SubsKey::new());
		assert_hub_props(&hub, 3, 3);

		hub.send(2);

		// The messages are still received
		assert_eq!(rx_03.next().await, Some(2));
		assert_eq!(rx_04.next().await, Some(2));

		// Perform a clean unsubscription
		std::mem::drop(rx_04);

		hub.send(3);

		// The messages are still received
		assert_eq!(rx_03.next().await, Some(3));

		std::mem::drop(rx_03);

		hub.send(4);

		// The stuck subscription is still there
		assert_hub_props(&hub, 1, 1);
	});
}

async fn add_some_subscribers_see_that_messages_are_delivered_and_unsubscribe(hub: &TestHub) {
	let rx_01 = hub.subscribe(SubsKey::new());
	let rx_02 = hub.subscribe(SubsKey::new());

	hub.send(1);
	hub.send(2);
	hub.send(3);

	assert_eq!(rx_01.take(3).collect::<Vec<_>>().await, vec![1, 2, 3]);

	hub.send(4);
	hub.send(5);
	hub.send(6);

	assert_eq!(rx_02.take(6).collect::<Vec<_>>().await, vec![1, 2, 3, 4, 5, 6]);
}

#[test]
fn t03() {
	block_on(async {
		// Create a Hub
		let hub = TestHub::new(TK);
		assert_hub_props(&hub, 0, 0);
		add_some_subscribers_see_that_messages_are_delivered_and_unsubscribe(&hub).await;
		assert_hub_props(&hub, 0, 0);

		assert!(catch_unwind(AssertUnwindSafe(
			|| hub.subscribe(SubsKey::new().with_panic(SubsKeyPanic::OnSubscribePanicBefore))
		))
		.is_err());

		assert_hub_props(&hub, 0, 0);
		add_some_subscribers_see_that_messages_are_delivered_and_unsubscribe(&hub).await;
		assert_hub_props(&hub, 0, 0);
	});
}

#[test]
fn t04() {
	block_on(async {
		let hub = TestHub::new(TK);

		assert_hub_props(&hub, 0, 0);
		add_some_subscribers_see_that_messages_are_delivered_and_unsubscribe(&hub).await;
		assert_hub_props(&hub, 0, 0);

		assert!(catch_unwind(AssertUnwindSafe(
			|| hub.subscribe(SubsKey::new().with_panic(SubsKeyPanic::OnSubscribePanicAfter))
		))
		.is_err());

		// the registry has panicked after it has added a subs-id into its internal storage — the
		// sinks do not leak, although the subscriptions storage contains some garbage
		assert_hub_props(&hub, 0, 1);
		add_some_subscribers_see_that_messages_are_delivered_and_unsubscribe(&hub).await;
		assert_hub_props(&hub, 0, 1);
	})
}

#[test]
fn t05() {
	block_on(async {
		let hub = TestHub::new(TK);

		assert_hub_props(&hub, 0, 0);
		add_some_subscribers_see_that_messages_are_delivered_and_unsubscribe(&hub).await;
		assert_hub_props(&hub, 0, 0);

		let rx_01 =
			hub.subscribe(SubsKey::new().with_panic(SubsKeyPanic::OnUnsubscribePanicBefore));

		assert_hub_props(&hub, 1, 1);
		add_some_subscribers_see_that_messages_are_delivered_and_unsubscribe(&hub).await;
		assert_hub_props(&hub, 1, 1);

		assert!(catch_unwind(AssertUnwindSafe(move || std::mem::drop(rx_01))).is_err());

		// the registry has panicked on-unsubscribe before it removed the subs-id from its internal
		// storage — the sinks do not leak, although the subscriptions storage contains some garbage
		assert_hub_props(&hub, 0, 1);
		add_some_subscribers_see_that_messages_are_delivered_and_unsubscribe(&hub).await;
		assert_hub_props(&hub, 0, 1);
	})
}

#[test]
fn t06() {
	block_on(async {
		let hub = TestHub::new(TK);

		assert_hub_props(&hub, 0, 0);
		add_some_subscribers_see_that_messages_are_delivered_and_unsubscribe(&hub).await;
		assert_hub_props(&hub, 0, 0);

		let rx_01 = hub.subscribe(SubsKey::new().with_panic(SubsKeyPanic::OnUnsubscribePanicAfter));

		assert_hub_props(&hub, 1, 1);
		add_some_subscribers_see_that_messages_are_delivered_and_unsubscribe(&hub).await;
		assert_hub_props(&hub, 1, 1);

		assert!(catch_unwind(AssertUnwindSafe(move || std::mem::drop(rx_01))).is_err());

		// the registry has panicked on-unsubscribe after it removed the subs-id from its internal
		// storage — the sinks do not leak, the subscriptions storage does not contain any garbage
		assert_hub_props(&hub, 0, 0);
		add_some_subscribers_see_that_messages_are_delivered_and_unsubscribe(&hub).await;
		assert_hub_props(&hub, 0, 0);
	})
}

#[test]
fn t07() {
	block_on(async {
		let hub = TestHub::new(TK);

		assert_hub_props(&hub, 0, 0);
		add_some_subscribers_see_that_messages_are_delivered_and_unsubscribe(&hub).await;
		assert_hub_props(&hub, 0, 0);

		let rx_01 = hub.subscribe(SubsKey::new().with_panic(SubsKeyPanic::OnDispatchPanicBefore));
		assert_hub_props(&hub, 1, 1);
		assert!(catch_unwind(AssertUnwindSafe(|| hub.send(1))).is_err());
		assert_hub_props(&hub, 1, 1);

		std::mem::drop(rx_01);
		assert_hub_props(&hub, 0, 0);
		add_some_subscribers_see_that_messages_are_delivered_and_unsubscribe(&hub).await;
		assert_hub_props(&hub, 0, 0);
	})
}

#[test]
fn t08() {
	block_on(async {
		let hub = TestHub::new(TK);

		assert_hub_props(&hub, 0, 0);
		add_some_subscribers_see_that_messages_are_delivered_and_unsubscribe(&hub).await;
		assert_hub_props(&hub, 0, 0);

		let rx_01 = hub.subscribe(SubsKey::new().with_panic(SubsKeyPanic::OnDispatchPanicAfter));
		assert_hub_props(&hub, 1, 1);
		assert!(catch_unwind(AssertUnwindSafe(|| hub.send(1))).is_err());
		assert_hub_props(&hub, 1, 1);

		std::mem::drop(rx_01);
		assert_hub_props(&hub, 0, 0);
		add_some_subscribers_see_that_messages_are_delivered_and_unsubscribe(&hub).await;
		assert_hub_props(&hub, 0, 0);
	})
}
