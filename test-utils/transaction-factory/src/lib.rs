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

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]

use std::collections::HashMap;
use std::sync::Arc;
use std::ops::Mul;
use std::fmt::Display;

use log::info;

use client::block_builder::api::BlockBuilder;
use client::runtime_api::ConstructRuntimeApi;
use consensus_common::{BlockOrigin, ImportBlock, ForkChoiceStrategy, SelectChain};
use consensus_common::block_import::BlockImport;
use parity_codec::{Decode, Encode};
use serde::Serialize;
use sr_primitives::traits::{As, Block, Header, ProvideRuntimeApi, SimpleArithmetic};
use substrate_service::{FactoryBlock, FactoryFullConfiguration, FullClient, new_client, ServiceFactory, ComponentClient, FullComponents};
pub use crate::modes::Mode;

mod modes;
mod complex_mode;
mod simple_modes;

pub trait RuntimeAdapter {
	type AccountId;
	type Extrinsic;
	type Balance;
	type Moment;
	type BlockNumber;
	type BlockId;
	type Hash;
	type Secret;
	type Index;
	type Phase;
	type Header;

	fn transfer_extrinsic(
		sender: &Self::AccountId,
		key: &Self::Secret,
		destination: &Self::AccountId,
		amount: Self::Balance,
		index: Self::Index,
		phase: Self::Phase,
		prior_block_hash: &Self::Hash,
	) -> Self::Extrinsic;

	fn timestamp_inherent(
		ts: Self::Moment,
		key: Self::Secret,
		phase: Self::Phase,
		prior_block_hash: &Self::Hash
	) -> Self::Extrinsic;

	fn minimum_balance() -> Self::Balance;
	fn minimum_period() -> Self::Moment;
	fn master_account_id() -> Self::AccountId;
	fn master_account_secret() -> Self::Secret;
	fn extract_timestamp(block_hash: Self::Hash) -> Self::Moment;
	fn extract_index(account_id: Self::AccountId, block_hash: Self::Hash) -> Self::Index;
	fn extract_phase(block_hash: Self::Hash) -> Self::Phase;
	fn gen_random_account_id(seed: u64) -> Self::AccountId;
	fn gen_random_account_secret(seed: u64) -> Self::Secret;
}

pub struct FactoryState {
	pub block_no: u64,
	block_in_round: u64,
	mode: Mode,
	rounds: u64,
	num: u64,
	index: u64,
	phase: u64,
	round: u64,
	start_number: u64,
}

/// Manufactures transactions. The exact amount depends on
/// `mode`, `num` and `rounds`.
pub fn factory<F, RA>(
	mut config: FactoryFullConfiguration<F>,
	mode: Mode,
	num: u64,
	rounds: u64,
) -> cli::error::Result<()>
where
	F: ServiceFactory,
	F::RuntimeApi: ConstructRuntimeApi<FactoryBlock<F>, FullClient<F>>,
	FullClient<F>: ProvideRuntimeApi,
	<FullClient<F> as ProvideRuntimeApi>::Api: BlockBuilder<FactoryBlock<F>>,

	RA: RuntimeAdapter,
	<RA as RuntimeAdapter>::AccountId: Display,
	<RA as RuntimeAdapter>::Balance: Display + Mul + As<u64>,
	<RA as RuntimeAdapter>::Extrinsic: Encode + Serialize,
	<RA as RuntimeAdapter>::Hash: From<primitives::H256> + Copy + Display,
	<RA as RuntimeAdapter>::Index: Copy + As<u64>,
	<RA as RuntimeAdapter>::Moment: SimpleArithmetic + Copy,
	<RA as RuntimeAdapter>::Phase: Copy + As<u64>,
{
	let client = new_client::<F>(&config)?;

	let select_chain = F::build_select_chain(&mut config, client.clone())?;
	let best_header = select_chain.best_chain().expect("Failed to fetch best header");
	let mut prior_block_hash: RA::Hash = best_header.hash().into();

	let mut last_ts = RA::extract_timestamp(prior_block_hash);

	let start_number: u64 = client.info()?.chain.best_number.as_();

	let mut curr = FactoryState {
		mode: mode.clone(),
		num: num,
		index: 0,
		phase: 0,
		round: 0,
		rounds: rounds,
		block_in_round: 0,
		block_no: 0,
		start_number: start_number,
	};

	while let Some((ts, block)) = match mode {
		Mode::MasterToNToM =>
			complex_mode::next::<F, RA>(&mut curr, &client, prior_block_hash, last_ts),
		_ =>
			simple_modes::next::<F, RA>(&mut curr, &client, prior_block_hash, last_ts)
	} {
			prior_block_hash = block.header().hash().into();
			import_block::<F>(&client, block);
			last_ts = ts;

			info!("Imported block at {}", curr.block_no);
	}

	Ok(())
}

/// Create a baked block from a transfer extrinsic and timestamp inherent.
pub fn create_block<F, RA>(
	client: &Arc<ComponentClient<FullComponents<F>>>,
	transfer: RA::Extrinsic,
	timestamp: RA::Extrinsic
)
-> <F as ServiceFactory>::Block where
	F: ServiceFactory,
	F::RuntimeApi: ConstructRuntimeApi<FactoryBlock<F>, FullClient<F>>,
	FullClient<F>: ProvideRuntimeApi,
	<FullClient<F> as ProvideRuntimeApi>::Api: BlockBuilder<FactoryBlock<F>>,

	RA: RuntimeAdapter,
	<RA as RuntimeAdapter>::Extrinsic: Encode + Serialize,
{
	let mut block = client.new_block().expect("Failed to create new block");
	block.push(
		Decode::decode(&mut &transfer.encode()[..])
			.expect("Failed to decode transfer extrinsic")
	).unwrap();

	block.push(
		Decode::decode(&mut &timestamp.encode()[..])
			.expect("Failed to decode timestamp extrinsic")
	).expect("Failed to push timestamp inherent into block");

	block.bake().expect("Failed to bake block")
}

fn import_block<F>(
	client: &Arc<ComponentClient<FullComponents<F>>>,
	block: <F as ServiceFactory>::Block
) -> () where
	F: ServiceFactory,
{
	let import = ImportBlock {
		origin: BlockOrigin::File,
		header: block.header().clone(),
		post_digests: Vec::new(),
		body: Some(block.extrinsics().to_vec()),
		finalized: false,
		justification: None,
		auxiliary: Vec::new(),
		fork_choice: ForkChoiceStrategy::LongestChain,
	};
	client.import_block(import, HashMap::new()).expect("Failed to import block");
}
