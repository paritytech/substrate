// Copyright 2019 Parity Technologies (UK) Ltd.
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

use client::block_builder::api::BlockBuilder;
use client::runtime_api::ConstructRuntimeApi;
use consensus_common::{
	BlockOrigin, BlockImportParams, InherentData, ForkChoiceStrategy,
	SelectChain
};
use consensus_common::block_import::BlockImport;
use parity_codec::{Decode, Encode};
use sr_primitives::generic::BlockId;
use sr_primitives::traits::{
	Block as BlockT, Header as HeaderT, ProvideRuntimeApi, SimpleArithmetic,
	One, Zero,
};
use substrate_service::{
	FactoryBlock, FactoryFullConfiguration, FullClient, new_client,
	ServiceFactory, ComponentClient, FullComponents};
pub use crate::modes::Mode;

pub mod modes;
mod complex_mode;
mod simple_modes;

pub trait RuntimeAdapter {
	type AccountId: Display;
	type Balance: Display + SimpleArithmetic + From<Self::Number>;
	type Block: BlockT;
	type Index: Copy;
	type Number: Display + PartialOrd + SimpleArithmetic + Zero + One;
	type Phase: Copy;
	type Secret;

	fn new(mode: Mode, rounds: u64, start_number: u64) -> Self;

	fn block_no(&self) -> Self::Number;
	fn block_in_round(&self) -> Self::Number;
	fn mode(&self) -> &Mode;
	fn num(&self) -> Self::Number;
	fn rounds(&self) -> Self::Number;
	fn round(&self) -> Self::Number;
	fn start_number(&self) -> Self::Number;

	fn set_block_in_round(&mut self, val: Self::Number);
	fn set_block_no(&mut self, val: Self::Number);
	fn set_round(&mut self, val: Self::Number);

	fn transfer_extrinsic(
		&self,
		sender: &Self::AccountId,
		key: &Self::Secret,
		destination: &Self::AccountId,
		amount: &Self::Balance,
		genesis_hash: &<Self::Block as BlockT>::Hash,
		prior_block_hash: &<Self::Block as BlockT>::Hash,
	) -> <Self::Block as BlockT>::Extrinsic;

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
/// `mode`, `num` and `rounds`.
pub fn factory<F, RA>(
	mut factory_state: RA,
	mut config: FactoryFullConfiguration<F>,
) -> cli::error::Result<()>
where
	F: ServiceFactory,
	F::RuntimeApi: ConstructRuntimeApi<FactoryBlock<F>, FullClient<F>>,
	FullClient<F>: ProvideRuntimeApi,
	<FullClient<F> as ProvideRuntimeApi>::Api: BlockBuilder<FactoryBlock<F>>,
	RA: RuntimeAdapter,
	<<RA as RuntimeAdapter>::Block as BlockT>::Hash: From<primitives::H256>,
{
	if *factory_state.mode() != Mode::MasterToNToM && factory_state.rounds() > RA::Number::one() {
		let msg = "The factory can only be used with rounds set to 1 in this mode.".into();
		return Err(cli::error::Error::Input(msg));
	}

	let client = new_client::<F>(&config)?;

	let select_chain = F::build_select_chain(&mut config, client.clone())?;

	let best_header: Result<<F::Block as BlockT>::Header, cli::error::Error> =
		select_chain.best_chain().map_err(|e| format!("{:?}", e).into());
	let mut best_hash = best_header?.hash();
	let best_block_id = BlockId::<F::Block>::hash(best_hash);
	let genesis_hash = client.block_hash(Zero::zero())?
		.expect("Genesis block always exists; qed").into();

	while let Some(block) = match factory_state.mode() {
		Mode::MasterToNToM => complex_mode::next::<F, RA>(
			&mut factory_state,
			&client,
			genesis_hash,
			best_hash.into(),
			best_block_id,
		),
		_ => simple_modes::next::<F, RA>(
			&mut factory_state,
			&client,
			genesis_hash,
			best_hash.into(),
			best_block_id,
		),
	} {
		best_hash = block.header().hash();
		import_block::<F>(&client, block);

		info!("Imported block at {}", factory_state.block_no());
	}

	Ok(())
}

/// Create a baked block from a transfer extrinsic and timestamp inherent.
pub fn create_block<F, RA>(
	client: &Arc<ComponentClient<FullComponents<F>>>,
	transfer: <RA::Block as BlockT>::Extrinsic,
	inherent_extrinsics: Vec<<F::Block as BlockT>::Extrinsic>,
) -> <F as ServiceFactory>::Block
where
	F: ServiceFactory,
	FullClient<F>: ProvideRuntimeApi,
	F::RuntimeApi: ConstructRuntimeApi<FactoryBlock<F>, FullClient<F>>,
	<FullClient<F> as ProvideRuntimeApi>::Api: BlockBuilder<FactoryBlock<F>>,
	RA: RuntimeAdapter,
{
	let mut block = client.new_block(Default::default()).expect("Failed to create new block");
	block.push(
		Decode::decode(&mut &transfer.encode()[..])
			.expect("Failed to decode transfer extrinsic")
	).expect("Failed to push transfer extrinsic into block");

	for inherent in inherent_extrinsics {
		block.push(inherent).expect("Failed ...");
	}

	block.bake().expect("Failed to bake block")
}

fn import_block<F>(
	client: &Arc<ComponentClient<FullComponents<F>>>,
	block: <F as ServiceFactory>::Block
) -> () where F: ServiceFactory
{
	let import = BlockImportParams {
		origin: BlockOrigin::File,
		header: block.header().clone(),
		post_digests: Vec::new(),
		body: Some(block.extrinsics().to_vec()),
		finalized: false,
		justification: None,
		auxiliary: Vec::new(),
		fork_choice: ForkChoiceStrategy::LongestChain,
	};
	(&**client).import_block(import, HashMap::new()).expect("Failed to import block");
}
