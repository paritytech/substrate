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
	Block as BlockT, Header as HeaderT, SimpleArithmetic, One, Zero,
};

pub mod automata;
mod simple_modes;

pub trait RuntimeAdapter {
	type AccountId: Display;
	type Balance: Display + SimpleArithmetic + From<Self::Number>;
	type Block: BlockT;
	type Index: Copy;
	type Number: Display + PartialOrd + SimpleArithmetic + Zero + One;
	type Phase: Copy;
	type Secret;

	fn new(tx_name: String, start_number: u64, automaton: automata::Automaton) -> Self;

	fn index(&self) -> u32;
	fn increase_index(&mut self);

	fn block_no(&self) -> Self::Number;
	fn block_in_round(&self) -> Self::Number;
	fn num(&self) -> Self::Number;
	fn round(&self) -> Self::Number;
	fn start_number(&self) -> Self::Number;

	fn set_block_in_round(&mut self, val: Self::Number);
	fn set_block_no(&mut self, val: Self::Number);
	fn set_round(&mut self, val: Self::Number);

	fn create_extrinsic(
		&mut self,
		sender: &Self::AccountId,
		key: &Self::Secret,
		destination: &Self::AccountId,
		amount: &Self::Balance,
		version: u32,
		genesis_hash: &<Self::Block as BlockT>::Hash,
		prior_block_hash: &<Self::Block as BlockT>::Hash,
	) -> Option<<Self::Block as BlockT>::Extrinsic>;

	fn inherent_extrinsics(&self) -> InherentData;

	fn minimum_balance() -> Self::Balance;
	fn master_account_id() -> Self::AccountId;
	fn master_account_secret() -> Self::Secret;
	fn extract_index(&self, account_id: &Self::AccountId, block_hash: &<Self::Block as BlockT>::Hash) -> Self::Index;
	fn extract_phase(&self, block_hash: <Self::Block as BlockT>::Hash) -> Self::Phase;
	fn gen_random_account_id(seed: &Self::Number) -> Self::AccountId;
	fn gen_random_account_secret(seed: &Self::Number) -> Self::Secret;
}

/// Manufactures transactions. The exact amount depends on
/// `num` and `rounds`.
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

	loop {
		if factory_state.block_no() >= factory_state.num() {
			break
		}
		if let Some(block) = create_block::<RA, _, _, _, _>(
			&mut factory_state,
			&client,
			version,
			genesis_hash,
			best_hash,
			best_block_id,
		) {
			factory_state.set_block_no(factory_state.block_no() + RA::Number::one());

			info!("Created block {} with hash {}.", factory_state.block_no(), best_hash);

			best_hash = block.header().hash();
			best_block_id = BlockId::<Block>::hash(best_hash);
			import_block(client.clone(), block);

			info!("Imported block at {}\n\n", factory_state.block_no());
		} else {
			break
		}
	}

	Ok(())
}

/// Create a baked block from a transfer extrinsic and timestamp inherent.
pub fn create_block<RA, Backend, Exec, Block, RtApi>(
	factory_state: &mut RA,
	client: &Arc<Client<Backend, Exec, Block, RtApi>>,	
	version: u32,
	genesis_hash: <RA::Block as BlockT>::Hash,
	prior_block_hash: <RA::Block as BlockT>::Hash,
	prior_block_id: BlockId<Block>,
) -> Option<Block>
where
	Block: BlockT,
	Exec: sc_client::CallExecutor<Block, Backend = Backend> + Send + Sync + Clone,
	Backend: sc_client_api::backend::Backend<Block> + Send,
	Client<Backend, Exec, Block, RtApi>: ProvideRuntimeApi<Block>,
	RtApi: ConstructRuntimeApi<Block, Client<Backend, Exec, Block, RtApi>> + Send + Sync,
	<Client<Backend, Exec, Block, RtApi> as ProvideRuntimeApi<Block>>::Api:
		BlockBuilder<Block, Error = sp_blockchain::Error> +
		ApiExt<Block, StateBackend = Backend::State>,
	RA: RuntimeAdapter,
{
	let mut block = client.new_block(Default::default()).expect("Failed to create new block");

	let seed = factory_state.start_number();

	let from = (RA::master_account_id(), RA::master_account_secret());
	let amount = RA::minimum_balance();

	let inherents = factory_state.inherent_extrinsics();
	let inherents = client.runtime_api().inherent_extrinsics(&prior_block_id, inherents)
		.expect("Failed to create inherent extrinsics");

	for _ in 0..7 { // TODO: Make this configurable.
		let to = RA::gen_random_account_id(&seed);
		if let Some(extrinsic) = factory_state.create_extrinsic(
			&from.0,
			&from.1,
			&to,
			&amount,
			version,
			&genesis_hash,
			&prior_block_hash,
		) {
			block.push(
				Decode::decode(&mut &extrinsic.encode()[..])
					.expect("Failed to decode extrinsic")
			).expect("Failed to push extrinsic into block");

			factory_state.increase_index();
		} else {
			return None
		}
	}

	for inherent in inherents {
		block.push(inherent).expect("Failed ...");
	}

	Some(block.build().expect("Failed to bake block").block)
}

fn import_block<Backend, Exec, Block, RtApi>(
	mut client: Arc<Client<Backend, Exec, Block, RtApi>>,
	block: Block
) -> () where
	Block: BlockT,
	Exec: sc_client::CallExecutor<Block> + Send + Sync + Clone,
	Backend: sc_client_api::backend::Backend<Block> + Send,
	Client<Backend, Exec, Block, RtApi>: ProvideRuntimeApi<Block>,
	<Client<Backend, Exec, Block, RtApi> as ProvideRuntimeApi<Block>>::Api:
		sp_api::Core<Block, Error = sp_blockchain::Error> +
		ApiExt<Block, StateBackend = Backend::State>,
{
	let import = BlockImportParams {
		origin: BlockOrigin::File,
		header: block.header().clone(),
		post_digests: Vec::new(),
		body: Some(block.extrinsics().to_vec()),
		storage_changes: None,
		finalized: false,
		justification: None,
		auxiliary: Vec::new(),
		fork_choice: ForkChoiceStrategy::LongestChain,
		allow_missing_state: false,
		import_existing: false,
	};
	client.import_block(import, HashMap::new()).expect("Failed to import block");
}
