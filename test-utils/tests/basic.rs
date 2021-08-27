// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use sc_service::{TaskExecutor, TaskType};

#[substrate_test_utils::test]
async fn basic_test(_: TaskExecutor) {
	assert!(true);
}

#[substrate_test_utils::test]
#[should_panic(expected = "boo!")]
async fn panicking_test(_: TaskExecutor) {
	panic!("boo!");
}

#[substrate_test_utils::test(flavor = "multi_thread", worker_threads = 1)]
async fn basic_test_with_args(_: TaskExecutor) {
	assert!(true);
}

#[substrate_test_utils::test]
async fn rename_argument(ex: TaskExecutor) {
	let ex2 = ex.clone();
	ex2.spawn(Box::pin(async { () }), TaskType::Blocking);
	assert!(true);
}

// NOTE: enable this test only after setting SUBSTRATE_TEST_TIMEOUT to a smaller value
//
// SUBSTRATE_TEST_TIMEOUT=1 cargo test -- --ignored timeout
#[substrate_test_utils::test]
#[should_panic(expected = "test took too long")]
#[ignore]
async fn timeout(_: TaskExecutor) {
	tokio::time::sleep(std::time::Duration::from_secs(
		std::env::var("SUBSTRATE_TEST_TIMEOUT")
			.expect("env var SUBSTRATE_TEST_TIMEOUT has been provided by the user")
			.parse::<u64>()
			.unwrap() + 1,
	))
	.await;
}
