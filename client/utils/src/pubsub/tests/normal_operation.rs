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

#[test]
fn positive_rx_receives_relevant_messages_and_terminates_upon_hub_drop() {
	block_on(async {
		let hub = TestHub::new(TK);
		assert_eq!(hub.subs_count(), 0);

		// No subscribers yet. That message is not supposed to get to anyone.
		hub.send(0);

		let mut rx_01 = hub.subscribe(SubsKey::new());
		assert_eq!(hub.subs_count(), 1);

		// That message is sent after subscription. Should be delivered into rx_01.
		hub.send(1);
		assert_eq!(Some(1), rx_01.next().await);

		// Hub is disposed. The rx_01 should be over after that.
		std::mem::drop(hub);

		assert!(!rx_01.is_terminated());
		assert_eq!(None, rx_01.next().await);
		assert!(rx_01.is_terminated());
	});
}

#[test]
fn positive_subs_count_is_correct_upon_drop_of_rxs() {
	block_on(async {
		let hub = TestHub::new(TK);
		assert_eq!(hub.subs_count(), 0);

		let rx_01 = hub.subscribe(SubsKey::new());
		assert_eq!(hub.subs_count(), 1);
		let rx_02 = hub.subscribe(SubsKey::new());
		assert_eq!(hub.subs_count(), 2);

		std::mem::drop(rx_01);
		assert_eq!(hub.subs_count(), 1);
		std::mem::drop(rx_02);
		assert_eq!(hub.subs_count(), 0);
	});
}

#[test]
fn positive_subs_count_is_correct_upon_drop_of_rxs_on_cloned_hubs() {
	block_on(async {
		let hub_01 = TestHub::new(TK);
		let hub_02 = hub_01.clone();
		assert_eq!(hub_01.subs_count(), 0);
		assert_eq!(hub_02.subs_count(), 0);

		let rx_01 = hub_02.subscribe(SubsKey::new());
		assert_eq!(hub_01.subs_count(), 1);
		assert_eq!(hub_02.subs_count(), 1);

		let rx_02 = hub_02.subscribe(SubsKey::new());
		assert_eq!(hub_01.subs_count(), 2);
		assert_eq!(hub_02.subs_count(), 2);

		std::mem::drop(rx_01);
		assert_eq!(hub_01.subs_count(), 1);
		assert_eq!(hub_02.subs_count(), 1);

		std::mem::drop(rx_02);
		assert_eq!(hub_01.subs_count(), 0);
		assert_eq!(hub_02.subs_count(), 0);
	});
}
