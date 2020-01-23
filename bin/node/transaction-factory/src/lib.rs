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

use codec::{Decode, Encode};
use structopt::clap::arg_enum;
use rand::seq::SliceRandom;
use log::info;

use sc_client::Client;
use sp_block_builder::BlockBuilder;
use sp_api::{ConstructRuntimeApi, ProvideRuntimeApi, ApiExt};
use sp_consensus::{
	BlockOrigin, BlockImportParams, InherentData, ForkChoiceStrategy,
	SelectChain
};
use sp_consensus::block_import::BlockImport;
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{
	Block as BlockT, Header as HeaderT, SimpleArithmetic, One, Zero,
};

pub mod automata;

pub trait Number: Display + PartialOrd + SimpleArithmetic + Zero + One {}

pub trait RuntimeAdapter {
	type AccountId: Display;
	type Balance: Display + SimpleArithmetic + From<Self::Number>;
	type Block: BlockT;
	type Index: Copy;
	type Number: ;
	type Phase: Copy;
	type Secret;

	fn new() -> Self;

	fn index(&self) -> u32;
	fn increase_index(&mut self);

	fn block_number(&self) -> u32;
	fn block_in_round(&self) -> Self::Number;
	fn round(&self) -> Self::Number;
	fn start_number(&self) -> Self::Number;

	fn set_block_in_round(&mut self, val: Self::Number);
	fn increase_block_number(&mut self);
	fn set_round(&mut self, val: Self::Number);

	fn create_extrinsic(
		&mut self,
		sender: &Self::AccountId,
		module: String,
		extrinsic_name: String,
		key: &Self::Secret,
		runtime_version: u32,
		genesis_hash: &<Self::Block as BlockT>::Hash,
		prior_block_hash: &<Self::Block as BlockT>::Hash,
	) -> <Self::Block as BlockT>::Extrinsic;

	fn all_modules(&self) -> Vec<String>;
	fn all_calls(&self, module: String) -> Vec<String>;

	fn inherent_extrinsics(&self) -> InherentData;

	fn minimum_balance() -> Self::Balance;
	fn master_account_id() -> Self::AccountId;
	fn master_account_secret() -> Self::Secret;
	fn extract_index(&self, account_id: &Self::AccountId, block_hash: &<Self::Block as BlockT>::Hash) -> Self::Index;
	fn extract_phase(&self, block_hash: <Self::Block as BlockT>::Hash) -> Self::Phase;
	fn gen_random_account_id(seed: &Self::Number) -> Self::AccountId;
	fn gen_random_account_secret(seed: &Self::Number) -> Self::Secret;
}

arg_enum! {
	#[derive(Debug, Clone, Copy)]
	pub enum Mode {
		Random,
		Sequential,
		Automata,
	}
}

#[derive(Debug, Clone)]
pub struct Options {
	pub bench_file: String,
	pub blocks: u32,
	pub tx_per_block: u32,
	pub mode: Mode,
}

pub struct FactoryState<RA, Backend, Exec, Block, RtApi, Sc> 
where 
	Block: BlockT,
{
	runtime_state: RA,
	automaton: automata::Automaton,
	client: Arc<Client<Backend, Exec, Block, RtApi>>,
	select_chain: Sc,
	options: Options,
}

impl<RA, Backend, Exec, Block, RtApi, Sc> FactoryState<RA, Backend, Exec, Block, RtApi, Sc>
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
	pub fn new(
		client: Arc<Client<Backend, Exec, Block, RtApi>>,
		select_chain: Sc,
		automaton: automata::Automaton,
		runtime_state: RA,
		options: Options,
	) -> Self {
		Self {
			client,
			select_chain,
			automaton,
			runtime_state,
			options,
		}
	}

	pub fn run(&mut self) -> sc_cli::error::Result<()> {
		let best_header = self.select_chain.best_chain()
			.map_err(|e| format!("{:?}", e))?;
		let mut best_hash = best_header.hash();
		let mut best_block_id = BlockId::<Block>::hash(best_hash);
		let runtime_version = self.client.runtime_version_at(&best_block_id)?.spec_version;
		let genesis_hash = self.client.block_hash(Zero::zero())?
			.expect("genesis should exist");
		let mut one = false;
		loop {
			if self.runtime_state.block_number() >= self.options.blocks {
				break
			}
			if let Some(block) = self.create_block(
				runtime_version,
				genesis_hash,
				best_hash,
				best_block_id,
			) {
				self.runtime_state.increase_block_number();

				info!("Created block {} with hash {}.",
					self.runtime_state.block_number(),
					best_hash,
				);
				if !one {
					best_hash = block.header().hash();
					best_block_id = BlockId::<Block>::hash(best_hash);
					one = true;
				}

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

				self.client.clone().import_block(import, HashMap::new())
					.expect("Failed to import block");

				info!("Imported block at {}\n\n", self.runtime_state.block_number());
			} else {
				break
			}
		}

		Ok(())
	}

	pub fn create_block(
		&mut self,
		runtime_version: u32,
		genesis_hash: <RA::Block as BlockT>::Hash,
		prior_block_hash: <RA::Block as BlockT>::Hash,
		prior_block_id: BlockId<Block>,
	) -> Option<Block> {
		let mut block = self.client.new_block_at(
			&prior_block_id,
			Default::default(),
			sp_consensus::RecordProof::No,
		).expect("Failed to create new block");
		let account_id = RA::master_account_id();
		let account_secret = RA::master_account_secret();

		let inherents = self.runtime_state.inherent_extrinsics();
		let inherents = self.client.runtime_api()
			.inherent_extrinsics(&prior_block_id, inherents)
			.expect("Failed to create inherent extrinsics");

		let mut tx_pushed = 0;

		while tx_pushed < self.options.tx_per_block {
			let next_state = match self.options.mode {
				Mode::Automata => self.automaton.next_state(),
				Mode::Random => self.random_state(),
				Mode::Sequential => self.next_sequential_state(),
			};

			if let Some((module, function, _args)) = next_state {
				if ["Timestamp"].contains(&module.as_str()) {
					continue
				}
				println!("Creating a {}::{} extrinsic. Extrinsic {}/{} in this block.",
					module,
					function,
					tx_pushed + 1,
					self.options.tx_per_block,
				);
				let extrinsic = self.runtime_state.create_extrinsic(
					&account_id,
					module,
					function,
					&account_secret,
					runtime_version,
					&genesis_hash,
					&prior_block_hash,
				);
				let e = Decode::decode(&mut &extrinsic.encode()[..])
					.expect("decode failed");
				match block.push(e) { // TODO: figure out heartbeat.
					Ok(_) => {
						self.runtime_state.increase_index();
						tx_pushed += 1;
					}
					Err(e) => println!("Error on push: {:?}", e),
				}
			} else {
				// We reset the automaton, comming back to starting state,
				// in order to get more extrinsics out of it.
				self.automaton.clear_usage();
			}
		}

		for inherent in inherents {
			block.push(inherent).expect("Failed ...");
		}

		Some(block.build().expect("Failed to bake block").block)
	}

	fn random_state(&self) -> Option<(String, String, Vec<String>)> {
		let modules = self.runtime_state.all_modules();
		loop {
			let random_module = modules.choose(&mut rand::thread_rng())
				.expect("failed to choose module");
			let calls = self.runtime_state.all_calls(random_module.to_string());

			if let Some(random_call) = calls.choose(&mut rand::thread_rng()) {
				return Some((random_module.clone(), random_call.clone(), vec![]))
			}
		}
	}

	/// This should iterate over all modules and all extrinsics.
	fn next_sequential_state(&self) -> Option<(String, String, Vec<String>)> {
		None
	}
}
