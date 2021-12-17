// Copyright 2020-2021 Parity Technologies (UK) Ltd.
// This file is part of Cumulus.

// Cumulus is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Cumulus is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Cumulus.  If not, see <http://www.gnu.org/licenses/>.

// use cumulus_primitives_core::{ParachainBlockData, PersistedValidationData};
// use cumulus_primitives_parachain_inherent::{ParachainInherentData, INHERENT_IDENTIFIER};
// use cumulus_test_relay_sproof_builder::RelayStateSproofBuilder;

// use sc_block_builder::{BlockBuilder, BlockBuilderProvider};
// use sp_api::ProvideRuntimeApi;
// use sp_runtime::{
// 	generic::BlockId,
// 	traits::{Block as BlockT, Header as HeaderT},
// };

// /// An extension for the Cumulus test client to init a block builder.
// pub trait InitBlockBuilder {
// 	/// Init a specific block builder that works for the test runtime.
// 	///
// 	/// This will automatically create and push the inherents for you to make the block
// 	/// valid for the test runtime.
// 	///
// 	/// You can use the relay chain state sproof builder to arrange required relay chain state or
// 	/// just use a default one.
// 	fn init_block_builder(
// 		&self,
// 		validation_data: Option<PersistedValidationData<PHash, PBlockNumber>>,
// 		relay_sproof_builder: RelayStateSproofBuilder,
// 	) -> sc_block_builder::BlockBuilder<Block, Client, Backend>;

// 	/// Init a specific block builder at a specific block that works for the test runtime.
// 	///
// 	/// Same as [`InitBlockBuilder::init_block_builder`] besides that it takes a
// 	/// [`BlockId`] to say which should be the parent block of the block that is being build.
// 	fn init_block_builder_at(
// 		&self,
// 		at: &BlockId<Block>,
// 		validation_data: Option<PersistedValidationData<PHash, PBlockNumber>>,
// 		relay_sproof_builder: RelayStateSproofBuilder,
// 	) -> sc_block_builder::BlockBuilder<Block, Client, Backend>;

// 	/// Init a specific block builder that works for the test runtime.
// 	///
// 	/// Same as [`InitBlockBuilder::init_block_builder`] besides that it takes a
// 	/// [`BlockId`] to say which should be the parent block of the block that is being build and
// 	/// it will use the given `timestamp` as input for the timestamp inherent.
// 	fn init_block_builder_with_timestamp(
// 		&self,
// 		at: &BlockId<Block>,
// 		validation_data: Option<PersistedValidationData<PHash, PBlockNumber>>,
// 		relay_sproof_builder: RelayStateSproofBuilder,
// 		timestamp: u64,
// 	) -> sc_block_builder::BlockBuilder<Block, Client, Backend>;
// }

// fn init_block_builder<'a>(
// 	client: &'a Client,
// 	at: &BlockId<Block>,
// 	validation_data: Option<PersistedValidationData<PHash, PBlockNumber>>,
// 	relay_sproof_builder: RelayStateSproofBuilder,
// 	timestamp: u64,
// ) -> BlockBuilder<'a, Block, Client, Backend> {
// 	let mut block_builder = client
// 		.new_block_at(at, Default::default(), true)
// 		.expect("Creates new block builder for test runtime");

// 	let mut inherent_data = sp_inherents::InherentData::new();

// 	inherent_data
// 		.put_data(sp_timestamp::INHERENT_IDENTIFIER, &timestamp)
// 		.expect("Put timestamp failed");
//use test_runtime_babe::AccountId;
// 	let (relay_parent_storage_root, relay_chain_state) =
// 		relay_sproof_builder.into_state_root_and_proof();

// 	let mut validation_data = validation_data.unwrap_or_default();
// 	assert_eq!(
// 		validation_data.relay_parent_storage_root,
// 		Default::default(),
// 		"Overriding the relay storage root is not implemented",
// 	);
// 	validation_data.relay_parent_storage_root = relay_parent_storage_root;

// 	inherent_data
// 		.put_data(
// 			INHERENT_IDENTIFIER,
// 			&ParachainInherentData {
// 				validation_data,
// 				relay_chain_state,
// 				downward_messages: Default::default(),
// 				horizontal_messages: Default::default(),
// 			},
// 		)
// 		.expect("Put validation function params failed");

// 	let inherents = block_builder.create_inherents(inherent_data).expect("Creates inherents");

// 	inherents
// 		.into_iter()
// 		.for_each(|ext| block_builder.push(ext).expect("Pushes inherent"));

// 	block_builder
// }

// impl InitBlockBuilder for Client {
// 	fn init_block_builder(
// 		&self,
// 		validation_data: Option<PersistedValidationData<PHash, PBlockNumber>>,
// 		relay_sproof_builder: RelayStateSproofBuilder,
// 	) -> BlockBuilder<Block, Client, Backend> {
// 		let chain_info = self.chain_info();
// 		self.init_block_builder_at(
// 			&BlockId::Hash(chain_info.best_hash),
// 			validation_data,
// 			relay_sproof_builder,
// 		)
// 	}

// 	fn init_block_builder_at(
// 		&self,
// 		at: &BlockId<Block>,
// 		validation_data: Option<PersistedValidationData<PHash, PBlockNumber>>,
// 		relay_sproof_builder: RelayStateSproofBuilder,
// 	) -> BlockBuilder<Block, Client, Backend> {
// 		let last_timestamp =
// 			self.runtime_api().get_last_timestamp(&at).expect("Get last timestamp");

// 		let timestamp = last_timestamp + test_runtime_babe::MinimumPeriod::get();

// 		init_block_builder(self, at, validation_data, relay_sproof_builder, timestamp)
// 	}

// 	fn init_block_builder_with_timestamp(
// 		&self,
// 		at: &BlockId<Block>,
// 		validation_data: Option<PersistedValidationData<PHash, PBlockNumber>>,
// 		relay_sproof_builder: RelayStateSproofBuilder,
// 		timestamp: u64,
// 	) -> sc_block_builder::BlockBuilder<Block, Client, Backend> {
// 		init_block_builder(self, at, validation_data, relay_sproof_builder, timestamp)
// 	}
// }

// /// Extension trait for the [`BlockBuilder`](sc_block_builder::BlockBuilder) to build directly a
// /// [`ParachainBlockData`].
// pub trait BuildParachainBlockData {
// 	/// Directly build the [`ParachainBlockData`] from the block that comes out of the block builder.
// 	fn build_parachain_block(self, parent_state_root: Hash) -> ParachainBlockData<Block>;
// }

// impl<'a> BuildParachainBlockData for sc_block_builder::BlockBuilder<'a, Block, Client, Backend> {
// 	fn build_parachain_block(self, parent_state_root: Hash) -> ParachainBlockData<Block> {
// 		let built_block = self.build().expect("Builds the block");

// 		let storage_proof = built_block
// 			.proof
// 			.expect("We enabled proof recording before.")
// 			.into_compact_proof::<<Header as HeaderT>::Hashing>(parent_state_root)
// 			.expect("Creates the compact proof");

// 		let (header, extrinsics) = built_block.block.deconstruct();
// 		ParachainBlockData::new(header, extrinsics, storage_proof)
// 	}
// }
