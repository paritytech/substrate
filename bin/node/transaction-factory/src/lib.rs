// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Simple transaction factory which distributes tokens from a master
//! account to a specified number of newly created accounts.
//!
//! The factory currently only works on an empty database!

use std::collections::HashMap;
use std::sync::Arc;
use std::cmp::PartialOrd;
use std::fmt::Display;

use log::info;

use sc_client::Client;
use sp_block_builder::BlockBuilder;
use sp_api::{ConstructRuntimeApi, ProvideRuntimeApi, ApiExt};
use sp_consensus::{
	BlockOrigin, BlockImportParams, InherentData, ForkChoiceStrategy,
	SelectChain
};
use sp_consensus::block_import::BlockImport;
use codec::{Decode, Encode};
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{
	Block as BlockT, Header as HeaderT, AtLeast32Bit, One, Zero,
};

pub trait RuntimeAdapter {
	type AccountId: Display;
	type Balance: Display + AtLeast32Bit + From<Self::Number>;
	type Block: BlockT;
	type Index: Copy;
	type Number: Display + PartialOrd + AtLeast32Bit + Zero + One;
	type Phase: Copy;
	type Secret;

	fn new(blocks: u32, transactions: u32) -> Self;

	fn blocks(&self) -> u32;
	fn transactions(&self) -> u32;

	fn block_number(&self) -> u32;
	fn set_block_number(&mut self, value: u32);

	fn transfer_extrinsic(
		&mut self,
		sender: &Self::AccountId,
		key: &Self::Secret,
		destination: &Self::AccountId,
		amount: &Self::Balance,
		version: u32,
		genesis_hash: &<Self::Block as BlockT>::Hash,
		prior_block_hash: &<Self::Block as BlockT>::Hash,
	) -> <Self::Block as BlockT>::Extrinsic;

	fn inherent_extrinsics(&self) -> InherentData;

	fn minimum_balance() -> Self::Balance;
	fn master_account_id() -> Self::AccountId;
	fn master_account_secret() -> Self::Secret;

	fn gen_random_account_id(seed: u32) -> Self::AccountId;
	fn gen_random_account_secret(seed: u32) -> Self::Secret;
}

/// Manufactures transactions. The exact amount depends on `num` and `rounds`.
pub fn factory<RA, Backend, Exec, Block, RtApi, Sc>(
	mut factory_state: RA,
	client: &Arc<Client<Backend, Exec, Block, RtApi>>,
	select_chain: &Sc,
) -> sc_cli::error::Result<()>
where
	Block: BlockT,
	Exec: sc_client::CallExecutor<Block, Backend = Backend> + Send + Sync + Clone,
	Backend: sc_client_api::backend::Backend<Block> + Send,
	Client<Backend, Exec, Block, RtApi>: ProvideRuntimeApi<Block>,
	<Client<Backend, Exec, Block, RtApi> as ProvideRuntimeApi<Block>>::Api:
		BlockBuilder<Block, Error = sp_blockchain::Error> +
		ApiExt<Block, StateBackend = Backend::State>,
	RtApi: ConstructRuntimeApi<Block, Client<Backend, Exec, Block, RtApi>> + Send + Sync,
	Sc: SelectChain<Block>,
	RA: RuntimeAdapter<Block = Block>,
	Block::Hash: From<sp_core::H256>,
{
	let best_header: Result<<Block as BlockT>::Header, sc_cli::error::Error> =
		select_chain.best_chain().map_err(|e| format!("{:?}", e).into());
	let mut best_hash = best_header?.hash();
	let mut best_block_id = BlockId::<Block>::hash(best_hash);
	let version = client.runtime_version_at(&best_block_id)?.spec_version;
	let genesis_hash = client.block_hash(Zero::zero())?
		.expect("Genesis block always exists; qed").into();

	while factory_state.block_number() < factory_state.blocks() {
		let from = (RA::master_account_id(), RA::master_account_secret());
		let amount = RA::minimum_balance();

		let inherents = RA::inherent_extrinsics(&factory_state);
		let inherents = client.runtime_api().inherent_extrinsics(&best_block_id, inherents)
			.expect("Failed to create inherent extrinsics");

		let tx_per_block = factory_state.transactions();

		let mut block = client.new_block(Default::default()).expect("Failed to create new block");

		for tx_num in 0..tx_per_block {
			let seed = tx_num * (factory_state.block_number() + 1);
			let to = RA::gen_random_account_id(seed);

			let transfer = factory_state.transfer_extrinsic(
				&from.0,
				&from.1,
				&to,
				&amount,
				version,
				&genesis_hash,
				&best_hash,
			);

			info!("Pushing transfer {}/{} to {} into block.", tx_num + 1, tx_per_block, to);

			block.push(
				Decode::decode(&mut &transfer.encode()[..])
					.expect("Failed to decode transfer extrinsic")
			).expect("Failed to push transfer extrinsic into block");
		}

		for inherent in inherents {
			block.push(inherent).expect("Failed ...");
		}

		let block = block.build().expect("Failed to bake block").block;

		factory_state.set_block_number(factory_state.block_number() + 1);

		info!(
			"Created block {} with hash {}.",
			factory_state.block_number(),
			best_hash,
		);

		best_hash = block.header().hash();
		best_block_id = BlockId::<Block>::hash(best_hash);

		let mut import = BlockImportParams::new(BlockOrigin::File, block.header().clone());
		import.body = Some(block.extrinsics().to_vec());
		import.fork_choice = Some(ForkChoiceStrategy::LongestChain);
		client.clone().import_block(import, HashMap::new()).expect("Failed to import block");

		info!("Imported block at {}", factory_state.block_number());
	}

	Ok(())
}
