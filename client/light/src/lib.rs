// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Light client components.

use sp_runtime::traits::{Block as BlockT, HashFor};
use std::sync::Arc;

pub mod backend;
pub mod blockchain;
pub mod call_executor;

pub use backend::*;
pub use blockchain::*;
pub use call_executor::*;

use sc_client_api::light::Storage as BlockchainStorage;

/// Create an instance of light client backend.
pub fn new_light_backend<B, S>(blockchain: Arc<Blockchain<S>>) -> Arc<Backend<S, HashFor<B>>>
where
	B: BlockT,
	S: BlockchainStorage<B>,
{
	Arc::new(Backend::new(blockchain))
}
