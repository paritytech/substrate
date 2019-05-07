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

//! Simple transaction factory which distributes tokens from Alice
//! to a specified number of newly created accounts.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]

use std::collections::HashMap;

use log::info;

use client::block_builder::api::BlockBuilder;
use client::runtime_api::ConstructRuntimeApi;
use consensus_common::{BlockOrigin, ImportBlock, ForkChoiceStrategy};
use consensus_common::block_import::BlockImport;
use parity_codec::{Decode, Encode};
use sr_primitives::traits::{As, Block, Header, ProvideRuntimeApi, SimpleArithmetic};
use substrate_service::{FactoryBlock, FactoryFullConfiguration, FullClient, new_client, ServiceFactory};

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

	fn transfer_extrinsic(
		sender: Self::AccountId,
		key: Self::Secret,
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
	fn extract_index(block_hash: Self::Hash) -> Self::Index;
	fn extract_phase(block_hash: Self::Hash) -> Self::Phase;
	fn gen_random_account_id(seed: u64) -> Self::AccountId;
}

/// Manufacture `num` transactions from Alice to `num` accounts.
pub fn factory<F, RA>(
	config: FactoryFullConfiguration<F>,
	num: u64,
) -> cli::error::Result<()>
where
	F: ServiceFactory,
	F::RuntimeApi: ConstructRuntimeApi<FactoryBlock<F>, FullClient<F>>,
	FullClient<F>: ProvideRuntimeApi,
	<FullClient<F> as ProvideRuntimeApi>::Api: BlockBuilder<FactoryBlock<F>>,

	RA: RuntimeAdapter,
	<RA as RuntimeAdapter>::Extrinsic: Encode,
	<RA as RuntimeAdapter>::AccountId: std::fmt::Display,
	<RA as RuntimeAdapter>::Hash: std::convert::From<primitives::H256> + Copy,
	<RA as RuntimeAdapter>::Hash: std::fmt::Display,
	<RA as RuntimeAdapter>::Moment: SimpleArithmetic + Copy,
	<RA as RuntimeAdapter>::Index: Copy + As<u64>,
	<RA as RuntimeAdapter>::Phase: Copy + As<u64>,
{
	info!("Creating {} transactions...", num);

	let client = new_client::<F>(&config)?;

	let mut prior_block_hash: RA::Hash = client.best_block_header()?.hash().into();
	let mut last_ts = RA::extract_timestamp(prior_block_hash);
	let mut index: u64 = RA::extract_index(prior_block_hash).as_();
	let mut phase: u64 = RA::extract_phase(prior_block_hash).as_();

	let start_number: u64 = client.info()?.chain.best_number.as_();
	let mut curr = start_number;

	while curr < start_number + num {
		info!("Creating block {}", curr);

		let mut block = client.new_block().expect("Failed to create new block");
		let to = RA::gen_random_account_id(curr);

		// index contains amount of prior transactions on this account
		// TODO fetch correct nonce and phase via api
		let transfer = RA::transfer_extrinsic(
			RA::master_account_id(),
			RA::master_account_secret(),
			&to,
			RA::minimum_balance(),
			RA::Index::sa(index),
			RA::Phase::sa(phase),
			&prior_block_hash,
		);

		block.push(
			Decode::decode(&mut &transfer.encode()[..])
				.expect("Failed to decode transfer extrinsic")
		).unwrap();

		let new_ts = last_ts + RA::minimum_period();
		let timestamp = RA::timestamp_inherent(
			new_ts.clone(),
			RA::master_account_secret(),
			RA::Phase::sa(phase),
			&prior_block_hash
		);
		block.push(
			Decode::decode(&mut &timestamp.encode()[..])
				.expect("Failed to decode timestamp extrinsic")
		).expect("Failed to push timestamp inherent into block");
		last_ts = new_ts;

		let block = block.bake().expect("Failed to bake block");
		prior_block_hash = block.header().hash().into();

		info!(
			"Created block {} with hash {}. Transferring from master account to {}.",
			curr + 1,
			prior_block_hash,
			to
		);

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

		info!("Imported block {}", curr + 1);

		curr += 1;
		phase += 1;
		index += 1;
	}

	info!("Finished importing {} blocks", curr);

	Ok(())
}
