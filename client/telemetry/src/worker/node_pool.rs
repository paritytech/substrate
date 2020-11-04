// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use crate::worker::{node::Node, WsTrans};
use libp2p::Multiaddr;
use parking_lot::Mutex;
use std::collections::{hash_map::Entry, HashMap};
use std::sync::Arc;

#[derive(Debug, Default)]
pub struct NodePool {
	nodes: Mutex<HashMap<Multiaddr, Arc<Mutex<Node<WsTrans>>>>>,
}

impl NodePool {
	pub fn get_or_create(
		&self,
		transport: WsTrans,
		addr: Multiaddr,
	) -> (Arc<Mutex<Node<WsTrans>>>, bool) {
		let mut nodes = self.nodes.lock();
		let entry = nodes.entry(addr.clone());
		let new = matches!(entry, Entry::Vacant(..));

		(
			entry
				.or_insert_with(|| Arc::new(Node::new(transport, addr).into()))
				.clone(),
			new,
		)
	}
}
