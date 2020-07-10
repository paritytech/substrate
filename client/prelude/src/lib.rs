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

pub use sc_service;
pub use sc_finality_grandpa;
pub use sc_consensus;
pub use sc_consensus_aura;
pub use sc_transaction_pool;
pub use sc_consensus_babe;

#[macro_export]
macro_rules! prelude {
    ($block:ty, $runtime_api:ty, $executor:ty) => {
        pub type FullClient = $crate::sc_service::TFullClient<$block, $runtime_api, $executor>;
        pub type FullBackend = $crate::sc_service::TFullBackend<$block>;
        pub type FullGrandpaBlockImport<SelectChain> = $crate::sc_finality_grandpa::GrandpaBlockImport<
            FullBackend, $block, FullClient, SelectChain
        >;
        pub type FullGrandpaLink<SelectChain> = $crate::sc_finality_grandpa::LinkHalf<
            $block, FullClient, SelectChain
        >;
        pub type FullLongestChain = $crate::sc_consensus::LongestChain<FullBackend, $block>;

        pub type FullBasicPool = $crate::sc_transaction_pool::BasicPool<
            sc_transaction_pool::FullChainApi<FullClient, $block>, $block
        >;

        pub type FullAuraImportQueue = $crate::sc_consensus_aura::AuraImportQueue<
            $block, sp_api::TransactionFor<FullClient, $block>
        >;

        pub type FullBabeImportQueue = $crate::sc_consensus_babe::BabeImportQueue<
            $block, sp_api::TransactionFor<FullClient, $block>
        >;

        pub type FullBabeBlockImport<BlockImport> = $crate::sc_consensus_babe::BabeBlockImport<
            $block, FullClient, BlockImport
        >;

        pub type BabeLink = $crate::sc_consensus_babe::BabeLink<$block>;

        pub type LightClient = $crate::sc_service::TLightClient<$block, $runtime_api, $executor>;
    }
}

#[cfg(test)]
mod tests {
    mod prelude {
        prelude!((), (), ());
    }
}
