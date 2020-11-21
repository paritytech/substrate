// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Tests for the module.

use super::*;
use mock::{Post, Balances, Test, Origin, new_test_ext};
use frame_support::{assert_ok, assert_noop};
use pallet_balances::Error as BalancesError;

#[test]
fn blog_post_lifecycle_works() {
	new_test_ext().execute_with(|| {
		let topic = b"hello".to_vec();
		let post = b"world".to_vec();
		// Create
		assert_ok!(Post::post(Origin::signed(1), PostType::Blog, topic.clone(), post.clone()));
		assert_eq!(Balances::reserved_balance(&1), (topic.len() + post.len()) as u64);
		assert!(Post::blog(&1, &topic).is_some());
		// Delete
		assert_ok!(Post::delete(Origin::signed(1), PostType::Blog, topic.clone()));
		assert_eq!(Balances::reserved_balance(&1), 0);
		assert!(Post::blog(&1, &topic).is_none());
	});
}

#[test]
fn thread_post_lifecycle_works() {
	new_test_ext().execute_with(|| {
		let topic = b"hello".to_vec();
		let post = b"world".to_vec();
		// Create
		assert_ok!(Post::post(Origin::signed(1), PostType::Thread, topic.clone(), post.clone()));
		assert_eq!(Balances::reserved_balance(&1), (topic.len() + post.len()) as u64);
		assert!(Post::thread(&topic, &1).is_some());
		// Delete
		assert_ok!(Post::delete(Origin::signed(1), PostType::Thread, topic.clone()));
		assert_eq!(Balances::reserved_balance(&1), 0);
		assert!(Post::thread(&topic, &1).is_none());
	});
}

#[test]
fn minimum_deposit_enforced() {
	new_test_ext().execute_with(|| {
		let topic = b"a".to_vec();
		let post = b"b".to_vec();
		assert_ok!(Post::post(Origin::signed(2), PostType::Blog, topic.clone(), post.clone()));
		assert_eq!(Balances::reserved_balance(&2), <Test as crate::Trait>::MinDeposit::get());
	});
}

#[test]
fn insufficient_funds_fails() {
	new_test_ext().execute_with(|| {
		let topic = b"a very long topic".to_vec();
		let post = b"and a very long post".to_vec();
		assert_noop!(
			Post::post(Origin::signed(1), PostType::Blog, topic, post),
			BalancesError::<Test, _>::InsufficientBalance,
		);
	});
}

#[test]
fn missing_post_not_found() {
	new_test_ext().execute_with(|| {
		let topic = b"404".to_vec();
		assert_noop!(
			Post::delete(Origin::signed(1), PostType::Blog, topic),
			Error::<Test>::NotFound,
		);
	});
}

#[test]
fn topic_too_large() {
	new_test_ext().execute_with(|| {
		let topic = vec![0u8; 101];
		let post = b"hello world".to_vec();
		assert_noop!(
			Post::post(Origin::signed(1), PostType::Blog, topic, post),
			Error::<Test>::TopicLength,
		);
	});
}

#[test]
fn post_too_large() {
	new_test_ext().execute_with(|| {
		let topic = b"hello world".to_vec();
		let post = vec![0u8; 1001];
		assert_noop!(
			Post::post(Origin::signed(1), PostType::Blog, topic, post),
			Error::<Test>::PostLength,
		);
	});
}
