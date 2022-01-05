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

use std::{collections::{HashMap, HashSet}, hash::Hash, sync::Arc};
use parking_lot::{MappedMutexGuard, Mutex, MutexGuard};
use trie_db::{TrieAccess, TrieRecorder, node::NodeOwned};

pub struct Recorder<H> {
	inner: Arc<Mutex<RecorderInner<H>>>,
}

impl<H> Recorder<H> where H: Eq + Hash + Clone {
	pub fn as_trie_recorder(&self) -> MutexGuard<impl TrieRecorder<H>> {
		self.inner.lock()
	}
}

struct RecorderInner<H> {
	accessed_keys: HashSet<Vec<u8>>,
	accessed_owned_nodes: HashMap<H, NodeOwned<H>>,
	accessed_encoded_nodes: HashMap<H, Vec<u8>>,
}

impl<H> trie_db::TrieRecorder<H> for RecorderInner<H> where H:Eq + Hash + Clone {
	fn record<'a>(&mut self, access: TrieAccess<'a, H>) {
		match access {
			TrieAccess::Key(key) => {
				self.accessed_keys.insert(key.into());
			},
			TrieAccess::NodeOwned { hash, node_owned } => {
				self.accessed_owned_nodes.entry(hash).or_insert_with(|| (*node_owned).clone());
			},
			TrieAccess::EncodedNode { hash, encoded_node } => {
				self.accessed_encoded_nodes
					.entry(hash)
					.or_insert_with(|| encoded_node.into_owned());
			},
		}
	}
}
