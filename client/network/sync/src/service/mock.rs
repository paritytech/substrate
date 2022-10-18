// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use libp2p::PeerId;
use sc_network_common::service::NetworkSyncForkRequest;
use sp_runtime::traits::{Block as BlockT, NumberFor};

mockall::mock! {
	pub ChainSyncInterface<B: BlockT> {}

	impl<B: BlockT + 'static> NetworkSyncForkRequest<B::Hash, NumberFor<B>>
		for ChainSyncInterface<B>
	{
		fn set_sync_fork_request(&self, peers: Vec<PeerId>, hash: B::Hash, number: NumberFor<B>);
	}
}
