// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use futures::StreamExt;

#[derive(Clone)]
pub struct DummyTracingKey;
impl TracingKeyStr for DummyTracingKey {
	const TRACING_KEY: &'static str = "test_notification_stream";
}

type StringStream = NotificationStream<String, DummyTracingKey>;

#[test]
fn notification_channel_simple() {
	let (sender, stream) = StringStream::channel();

	let test_payload = String::from("test payload");
	let closure_payload = test_payload.clone();

	// Create a future to receive a single notification
	// from the stream and verify its payload.
	let future = stream.subscribe(100_000).take(1).for_each(move |payload| {
		let test_payload = closure_payload.clone();
		async move {
			assert_eq!(payload, test_payload);
		}
	});

	// Send notification.
	let r: std::result::Result<(), ()> = sender.notify(|| Ok(test_payload));
	r.unwrap();

	// Run receiver future.
	tokio_test::block_on(future);
}
