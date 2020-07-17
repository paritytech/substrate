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

pub use sc_service as _service;
pub use sc_finality_grandpa as _grandpa;
pub use sc_consensus as _consensus;
pub use sc_consensus_aura as _aura;
pub use sc_consensus_babe as _babe;
pub use sc_transaction_pool as _transaction_pool;
pub use sc_network as _network;
pub use sp_api as _sp_api;

#[macro_export]
macro_rules! setup_types {
    ($block:ty, $runtime_api:ty, $executor:ty) => {
        use $crate::{
            _service as service, _grandpa as grandpa, _consensus as consensus, _aura as aura,
            _transaction_pool as transaction_pool, _sp_api as sp_api, _network as network,
            _babe as babe,
        };

        /// Type definitions for a full client.
        pub mod full {
            use super::*;

            /// A full client.
            pub type Client = service::TFullClient<$block, $runtime_api, $executor>;
            /// A full backend.
            pub type Backend = service::TFullBackend<$block>;
            /// A GRANDPA block import.
            pub type GrandpaBlockImport<SelectChain> = grandpa::GrandpaBlockImport<
                Backend, $block, Client, SelectChain
            >;
            /// A GRANDPA link. Connects the block import to the GRANDPA service.
            pub type GrandpaLink<SelectChain> = grandpa ::LinkHalf<
                $block, Client, SelectChain
            >;
            /// A basic select chain implementation.
            pub type LongestChain = consensus::LongestChain<Backend, $block>;
            /// A basic transaction pool.
            pub type BasicPool = transaction_pool::BasicPool<
                transaction_pool::FullChainApi<Client, $block>, $block
            >;
            /// An import queue for AURA.
            pub type AuraImportQueue = aura::AuraImportQueue<
                $block, sp_api::TransactionFor<Client, $block>
            >;
            /// An import queue for BABE.
            pub type BabeImportQueue = babe::BabeImportQueue<
                $block, sp_api::TransactionFor<Client, $block>
            >;
            /// A block import for BABE. Wraps around another block import.
            pub type BabeBlockImport<BlockImport> = babe::BabeBlockImport<
                $block, Client, BlockImport
            >;
        }
        
        /// Type definitions for a light client.
        pub mod light {
            use super::*;

            /// A light client.
            pub type Client = service::TLightClient<$block, $runtime_api, $executor>;
            /// A network fetcher for a light client.
            pub type Fetcher = network::config::OnDemand<$block>;
            /// A basic transaction pool.
            pub type BasicPool = transaction_pool::BasicPool<
                transaction_pool::LightChainApi<Client, Fetcher, $block>, $block
            >;
        }       
    }
}

#[cfg(test)]
mod tests {
    mod prelude {
        setup_types!((), (), ());
    }
}
