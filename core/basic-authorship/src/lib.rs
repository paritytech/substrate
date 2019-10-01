// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Basic implementation of block-authoring logic.
//!
//! # Example
//!
//! ```
//! # use substrate_basic_authorship::ProposerFactory;
//! # use consensus_common::{Environment, Proposer};
//! # use sr_primitives::generic::BlockId;
//! # use std::{sync::Arc, time::Duration};
//! # use test_client::{self, runtime::{Extrinsic, Transfer}, AccountKeyring};
//! # use transaction_pool::txpool::{self, Pool as TransactionPool};
//! # let client = Arc::new(test_client::new());
//! # let chain_api = transaction_pool::FullChainApi::new(client.clone());
//! # let txpool = Arc::new(TransactionPool::new(Default::default(), chain_api));
//! // The first step is to create a `ProposerFactory`.
//! let mut proposer_factory = ProposerFactory {
//! 	client: client.clone(),
//! 	transaction_pool: txpool.clone(),
//! };
//!
//! // From this factory, we create a `Proposer`.
//! let mut proposer = proposer_factory.init(
//! 	&client.header(&BlockId::number(0)).unwrap().unwrap(),
//! ).unwrap();
//!
//! // This `Proposer` allows us to create a block proposition.
//! // The proposer will grab transactions from the transaction pool, and put them into the block.
//! let future = proposer.propose(
//! 	Default::default(),
//! 	Default::default(),
//! 	Duration::from_secs(2)
//! );
//!
//! // We wait until the proposition is performed.
//! let block = futures::executor::block_on(future).unwrap();
//! println!("Generated block: {:?}", block);
//! ```
//!

mod basic_authorship;

pub use crate::basic_authorship::{ProposerFactory, Proposer};
