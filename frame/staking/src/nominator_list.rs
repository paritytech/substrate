// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Provide a linked list of nominators, sorted by stake.

use crate::Config;

// TODOS:
//
// - storage map for nodes
// - storage value for list
// - shorthand access to the list itself
// - basic operations
//   - shorthand access for the account, prev, next
// - iterator or cursor
// - update `ElectionDataProvider` impl to use the nominator list to count off the top N

type AccountIdOf<T> = <T as frame_system::Config>::AccountId;

/// Linked list of nominstors, sorted by stake.
pub struct NominatorList<T: Config> {
	head: Option<AccountIdOf<T>>,
	tail: Option<AccountIdOf<T>>,
}

struct Node<T: Config> {
	account: AccountIdOf<T>,
	prev: Option<AccountIdOf<T>>,
	next: Option<AccountIdOf<T>>,
}
