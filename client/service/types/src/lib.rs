// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Type definitions to make building a service easier.

#![warn(missing_docs)]

pub use sc_service as _service;
pub use sc_finality_grandpa as _grandpa;
pub use sc_consensus as _consensus;
pub use sc_consensus_aura as _aura;
pub use sc_consensus_babe as _babe;
pub use sc_transaction_pool as _transaction_pool;
pub use sc_network as _network;
pub use sp_api as _sp_api;

use {
    _service as service, _grandpa as grandpa, _consensus as consensus, _aura as aura,
    _transaction_pool as transaction_pool, _sp_api as sp_api, _network as network,
    _babe as babe,
};

/// Type definitions for a full client.
pub mod full {
    use super::*;

    pub use service::TFullClient as Client;
    pub use service::TFullBackend as Backend;

    /// A GRANDPA block import.
    pub type GrandpaBlockImport<Block, RuntimeApi, Executor, SelectChain> = grandpa::GrandpaBlockImport<
        Backend<Block>, Block, Client<Block, RuntimeApi, Executor>, SelectChain
    >;
    /// A GRANDPA link. Connects the block import to the GRANDPA service.
    pub type GrandpaLink<Block, RuntimeApi, Executor, SelectChain> = grandpa ::LinkHalf<
        Block, Client<Block, RuntimeApi, Executor>, SelectChain
    >;
    /// A basic select chain implementation.
    pub type LongestChain<Block> = consensus::LongestChain<Backend<Block>, Block>;
    /// A basic transaction pool.
    pub type BasicPool<Block, RuntimeApi, Executor> = transaction_pool::BasicPool<
        transaction_pool::FullChainApi<Client<Block, RuntimeApi, Executor>, Block>, Block
    >;
    /// An import queue for AURA.
    pub type AuraImportQueue<Block, RuntimeApi, Executor> = aura::AuraImportQueue<
        Block, sp_api::TransactionFor<Client<Block, RuntimeApi, Executor>, Block>
    >;
    /// An import queue for BABE.
    pub type BabeImportQueue<Block, RuntimeApi, Executor> = babe::BabeImportQueue<
        Block, sp_api::TransactionFor<Client<Block, RuntimeApi, Executor>, Block>
    >;
    /// A block import for BABE. Wraps around another block import.
    pub type BabeBlockImport<Block, RuntimeApi, Executor, BlockImport> = babe::BabeBlockImport<
        Block, Client<Block, RuntimeApi, Executor>, BlockImport
    >;
}

/// Type definitions for a light client.
pub mod light {
    use super::*;

    pub use service::TLightClient as Client;
    pub use service::TLightBackend as Backend;

    /// A network fetcher for a light client.
    pub type Fetcher<Block> = network::config::OnDemand<Block>;

    /// A basic transaction pool.
    pub type BasicPool<Block, RuntimeApi, Executor> = transaction_pool::BasicPool<
        transaction_pool::LightChainApi<Client<Block, RuntimeApi, Executor>, Fetcher<Block>, Block>,
        Block
    >;
}

/// Setup the type definitions given a `Block`, `RuntimeApi`and `Executor`.
#[macro_export]
macro_rules! setup_types {
    ($block:ty, $runtime_api:ty, $executor:ty) => {
        /// Type definitions for a full client.
        pub mod full {
            use $crate::full;
            use super::*;

            /// A full client.
            pub type Client = full::Client<$block, $runtime_api, $executor>;
            /// A full backend.
            pub type Backend = full::Backend<$block>;
            /// A GRANDPA block import.
            pub type GrandpaBlockImport<SelectChain> = full::GrandpaBlockImport<
                $block, $runtime_api, $executor, SelectChain
            >;
            /// A GRANDPA link. Connects the block import to the GRANDPA service.
            pub type GrandpaLink<SelectChain> = full::GrandpaLink<
                $block, $runtime_api, $executor, SelectChain
            >;
            /// A basic select chain implementation.
            pub type LongestChain = full::LongestChain<$block>;
            /// A basic transaction pool.
            pub type BasicPool = $crate::BasicPool<$block, $runtime_api, $executor>;
            /// An import queue for AURA.
            pub type AuraImportQueue = full::AuraImportQueue<
                $block, $runtime_api, $executor
            >;
            /// An import queue for BABE.
            pub type BabeImportQueue = full::BabeImportQueue<
                $block, $runtime_api, $executor
            >;
            /// A block import for BABE. Wraps around another block import.
            pub type BabeBlockImport<BlockImport> = full::BabeBlockImport<
                $block, $runtime_api, $executor, BlockImport
            >;
        }
        
        /// Type definitions for a light client.
        pub mod light {
            use $crate::light;
            use super::*;

            /// A light client.
            pub type Client = light::Client<$block, $runtime_api, $executor>;
            /// A network fetcher for a light client.
            pub type Fetcher = light::Fetcher<$block>;
            /// A basic transaction pool.
            pub type BasicPool = light::BasicPool<$block, $runtime_api, $executor>;
        }       
    }
}

#[cfg(test)]
mod tests {
    mod prelude {
        setup_types!((), (), ());
    }
}
