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

pub use service;
pub use grandpa;
pub use consensus;
pub use aura;
pub use transaction_pool;
pub use babe;
pub use network;

#[macro_export]
macro_rules! setup_types {
    ($block:ty, $runtime_api:ty, $executor:ty) => {
        pub mod full {
            use super::*;

            pub type Client = $crate::service::TFullClient<$block, $runtime_api, $executor>;
            pub type Backend = $crate::service::TFullBackend<$block>;
            pub type GrandpaBlockImport<SelectChain> = $crate::grandpa::GrandpaBlockImport<
                Backend, $block, Client, SelectChain
            >;
            pub type GrandpaLink<SelectChain> = $crate::grandpa ::LinkHalf<
                $block, Client, SelectChain
            >;
            pub type LongestChain = $crate::consensus::LongestChain<Backend, $block>;

            pub type BasicPool = $crate::transaction_pool::BasicPool<
                sc_transaction_pool::FullChainApi<Client, $block>, $block
            >;

            pub type AuraImportQueue = $crate::aura::AuraImportQueue<
                $block, sp_api::TransactionFor<Client, $block>
            >;

            pub type BabeImportQueue = $crate::babe::BabeImportQueue<
                $block, sp_api::TransactionFor<Client, $block>
            >;

            pub type BabeBlockImport<BlockImport> = $crate::babe::BabeBlockImport<
                $block, Client, BlockImport
            >;
        }
        
        pub type BabeLink = $crate::babe::BabeLink<$block>;

        pub mod light {
            use super::*;
            
            pub type Client = $crate::service::TLightClient<$block, $runtime_api, $executor>;
            pub type Fetcher = $crate::network::config::OnDemand<$block>;

            pub type BasicPool = $crate::transaction_pool::BasicPool<
                sc_transaction_pool::LightChainApi<Client, Fetcher, $block>, $block
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
