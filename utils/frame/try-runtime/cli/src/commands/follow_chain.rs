// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
	build_executor, ensure_matching_spec, extract_code, full_extensions, local_spec, parse,
	state_machine_call_with_proof, SharedParams, LOG_TARGET,
};
use jsonrpsee::{
	core::{
		async_trait,
		client::{Client, Subscription, SubscriptionClientT},
	},
	ws_client::WsClientBuilder,
};
use parity_scale_codec::{Decode, Encode};
use remote_externalities::{rpc_api::RpcService, Builder, Mode, OnlineConfig};
use sc_executor::NativeExecutionDispatch;
use sc_service::Configuration;
use serde::de::DeserializeOwned;
use sp_core::H256;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use sp_weights::Weight;
use std::{collections::VecDeque, fmt::Debug, str::FromStr};

const SUB: &str = "chain_subscribeFinalizedHeads";
const UN_SUB: &str = "chain_unsubscribeFinalizedHeads";

/// Configurations of the [`Command::FollowChain`].
#[derive(Debug, Clone, clap::Parser)]
pub struct FollowChainCmd {
	/// The url to connect to.
	#[clap(short, long, parse(try_from_str = parse::url))]
	uri: String,

	/// If set, then the state root check is enabled.
	#[clap(long)]
	state_root_check: bool,

	/// Which try-state targets to execute when running this command.
	///
	/// Expected values:
	/// - `all`
	/// - `none`
	/// - A comma separated list of pallets, as per pallet names in `construct_runtime!()` (e.g.
	///   `Staking, System`).
	/// - `rr-[x]` where `[x]` is a number. Then, the given number of pallets are checked in a
	///   round-robin fashion.
	#[clap(long, default_value = "none")]
	try_state: frame_try_runtime::TryStateSelect,

	/// If present, a single connection to a node will be kept and reused for fetching blocks.
	#[clap(long)]
	keep_connection: bool,
}

/// Start listening for with `SUB` at `url`.
///
/// Returns a pair `(client, subscription)` - `subscription` alone will be useless, because it
/// relies on the related alive `client`.
async fn start_subscribing<Header: DeserializeOwned>(
	url: &str,
) -> sc_cli::Result<(Client, Subscription<Header>)> {
	let client = WsClientBuilder::default()
		.connection_timeout(std::time::Duration::new(20, 0))
		.max_notifs_per_subscription(1024)
		.max_request_body_size(u32::MAX)
		.build(url)
		.await
		.map_err(|e| sc_cli::Error::Application(e.into()))?;

	log::info!(target: LOG_TARGET, "subscribing to {:?} / {:?}", SUB, UN_SUB);

	let sub = client
		.subscribe(SUB, None, UN_SUB)
		.await
		.map_err(|e| sc_cli::Error::Application(e.into()))?;
	Ok((client, sub))
}

/// Abstraction over RPC calling for headers.
#[async_trait]
trait HeaderProvider<Block: BlockT>
where
	Block::Header: HeaderT,
{
	/// Awaits for the header of the block with hash `hash`.
	async fn get_header(&self, hash: Block::Hash) -> Block::Header;
}

#[async_trait]
impl<Block: BlockT> HeaderProvider<Block> for RpcService
where
	Block::Header: DeserializeOwned,
{
	async fn get_header(&self, hash: Block::Hash) -> Block::Header {
		self.get_header::<Block>(hash).await.unwrap()
	}
}

/// Abstraction over RPC subscription for finalized headers.
#[async_trait]
trait HeaderSubscription<Block: BlockT>
where
	Block::Header: HeaderT,
{
	/// Await for the next finalized header from the subscription.
	///
	/// Returns `None` if either the subscription has been closed or there was an error when reading
	/// an object from the client.
	async fn next_header(&mut self) -> Option<Block::Header>;
}

#[async_trait]
impl<Block: BlockT> HeaderSubscription<Block> for Subscription<Block::Header>
where
	Block::Header: DeserializeOwned,
{
	async fn next_header(&mut self) -> Option<Block::Header> {
		match self.next().await {
			Some(Ok(header)) => Some(header),
			None => {
				log::warn!("subscription closed");
				None
			},
			Some(Err(why)) => {
				log::warn!("subscription returned error: {:?}. Probably decoding has failed.", why);
				None
			},
		}
	}
}

/// Stream of all finalized headers.
///
/// Returned headers are guaranteed to be ordered. There are no missing headers (even if some of
/// them lack justification).
struct FinalizedHeaders<'a, Block: BlockT, HP: HeaderProvider<Block>, HS: HeaderSubscription<Block>>
{
	header_provider: &'a HP,
	subscription: HS,
	fetched_headers: VecDeque<Block::Header>,
	last_returned: Option<<Block::Header as HeaderT>::Hash>,
}

impl<'a, Block: BlockT, HP: HeaderProvider<Block>, HS: HeaderSubscription<Block>>
	FinalizedHeaders<'a, Block, HP, HS>
where
	<Block as BlockT>::Header: DeserializeOwned,
{
	pub fn new(header_provider: &'a HP, subscription: HS) -> Self {
		Self {
			header_provider,
			subscription,
			fetched_headers: VecDeque::new(),
			last_returned: None,
		}
	}

	/// Reads next finalized header from the subscription. If some headers (without justification)
	/// have been skipped, fetches them as well. Returns number of headers that have been fetched.
	///
	/// All fetched headers are stored in `self.fetched_headers`.
	async fn fetch(&mut self) -> usize {
		let last_finalized = match self.subscription.next_header().await {
			Some(header) => header,
			None => return 0,
		};

		self.fetched_headers.push_front(last_finalized.clone());

		let mut last_finalized_parent = *last_finalized.parent_hash();
		let last_returned = self.last_returned.unwrap_or(last_finalized_parent);

		while last_finalized_parent != last_returned {
			let parent_header = self.header_provider.get_header(last_finalized_parent).await;
			self.fetched_headers.push_front(parent_header.clone());
			last_finalized_parent = *parent_header.parent_hash();
		}

		self.fetched_headers.len()
	}

	/// Get the next finalized header.
	pub async fn next(&mut self) -> Option<Block::Header> {
		if self.fetched_headers.is_empty() {
			self.fetch().await;
		}

		if let Some(header) = self.fetched_headers.pop_front() {
			self.last_returned = Some(header.hash());
			Some(header)
		} else {
			None
		}
	}
}

pub(crate) async fn follow_chain<Block, ExecDispatch>(
	shared: SharedParams,
	command: FollowChainCmd,
	config: Configuration,
) -> sc_cli::Result<()>
where
	Block: BlockT<Hash = H256> + DeserializeOwned,
	Block::Hash: FromStr,
	Block::Header: DeserializeOwned,
	<Block::Hash as FromStr>::Err: Debug,
	NumberFor<Block>: FromStr,
	<NumberFor<Block> as FromStr>::Err: Debug,
	ExecDispatch: NativeExecutionDispatch + 'static,
{
	let mut maybe_state_ext = None;
	let (_client, subscription) = start_subscribing::<Block::Header>(&command.uri).await?;

	let (code_key, code) = extract_code(&config.chain_spec)?;
	let executor = build_executor::<ExecDispatch>(&shared, &config);
	let execution = shared.execution;

	let rpc_service = RpcService::new(&command.uri, command.keep_connection).await?;

	let mut finalized_headers: FinalizedHeaders<Block, RpcService, Subscription<Block::Header>> =
		FinalizedHeaders::new(&rpc_service, subscription);

	while let Some(header) = finalized_headers.next().await {
		let hash = header.hash();
		let number = header.number();

		let block = rpc_service.get_block::<Block>(hash).await.unwrap();

		log::debug!(
			target: LOG_TARGET,
			"new block event: {:?} => {:?}, extrinsics: {}",
			hash,
			number,
			block.extrinsics().len()
		);

		// create an ext at the state of this block, whatever is the first subscription event.
		if maybe_state_ext.is_none() {
			let builder = Builder::<Block>::new()
				.mode(Mode::Online(OnlineConfig {
					transport: command.uri.clone().into(),
					at: Some(*header.parent_hash()),
					..Default::default()
				}))
				.state_version(shared.state_version);

			let new_ext = builder
				.inject_hashed_key_value(&[(code_key.clone(), code.clone())])
				.build()
				.await?;
			log::info!(
				target: LOG_TARGET,
				"initialized state externalities at {:?}, storage root {:?}",
				number,
				new_ext.as_backend().root()
			);

			let (expected_spec_name, expected_spec_version, spec_state_version) =
				local_spec::<Block, ExecDispatch>(&new_ext, &executor);
			ensure_matching_spec::<Block>(
				command.uri.clone(),
				expected_spec_name,
				expected_spec_version,
				shared.no_spec_check_panic,
			)
			.await;

			maybe_state_ext = Some((new_ext, spec_state_version));
		}

		let (state_ext, spec_state_version) =
			maybe_state_ext.as_mut().expect("state_ext either existed or was just created");

		let (mut changes, encoded_result) = state_machine_call_with_proof::<Block, ExecDispatch>(
			state_ext,
			&executor,
			execution,
			"TryRuntime_execute_block",
			(block, command.state_root_check, command.try_state.clone()).encode().as_ref(),
			full_extensions(),
		)?;

		let consumed_weight = <Weight as Decode>::decode(&mut &*encoded_result)
			.map_err(|e| format!("failed to decode weight: {:?}", e))?;

		let storage_changes = changes
			.drain_storage_changes(
				&state_ext.backend,
				&mut Default::default(),
				// Note that in case a block contains a runtime upgrade,
				// state version could potentially be incorrect here,
				// this is very niche and would only result in unaligned
				// roots, so this use case is ignored for now.
				*spec_state_version,
			)
			.unwrap();
		state_ext.backend.apply_transaction(
			storage_changes.transaction_storage_root,
			storage_changes.transaction,
		);

		log::info!(
			target: LOG_TARGET,
			"executed block {}, consumed weight {}, new storage root {:?}",
			number,
			consumed_weight,
			state_ext.as_backend().root(),
		);
	}

	log::error!(target: LOG_TARGET, "ws subscription must have terminated.");
	Ok(())
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::testing::{Block as TBlock, ExtrinsicWrapper, Header};
	use std::sync::Arc;
	use tokio::sync::Mutex;

	type Block = TBlock<ExtrinsicWrapper<()>>;
	type BlockNumber = u64;
	type Hash = H256;

	struct MockHeaderProvider(pub Arc<Mutex<VecDeque<BlockNumber>>>);

	fn headers() -> Vec<Header> {
		let mut headers = vec![Header::new_from_number(0)];
		for n in 1..11 {
			headers.push(Header {
				parent_hash: headers.last().unwrap().hash(),
				..Header::new_from_number(n)
			})
		}
		headers
	}

	#[async_trait]
	impl HeaderProvider<Block> for MockHeaderProvider {
		async fn get_header(&self, _hash: Hash) -> Header {
			let height = self.0.lock().await.pop_front().unwrap();
			headers()[height as usize].clone()
		}
	}

	struct MockHeaderSubscription(pub VecDeque<BlockNumber>);

	#[async_trait]
	impl HeaderSubscription<Block> for MockHeaderSubscription {
		async fn next_header(&mut self) -> Option<Header> {
			self.0.pop_front().map(|h| headers()[h as usize].clone())
		}
	}

	#[tokio::test]
	async fn finalized_headers_works_when_every_block_comes_from_subscription() {
		let heights = vec![4, 5, 6, 7];

		let provider = MockHeaderProvider(Default::default());
		let subscription = MockHeaderSubscription(heights.clone().into());
		let mut headers = FinalizedHeaders::new(&provider, subscription);

		for h in heights {
			assert_eq!(h, headers.next().await.unwrap().number);
		}
		assert_eq!(None, headers.next().await);
	}

	#[tokio::test]
	async fn finalized_headers_come_from_subscription_and_provider_if_in_need() {
		let all_heights = 3..11;
		let heights_in_subscription = vec![3, 4, 6, 10];
		// Consecutive headers will be requested in the reversed order.
		let heights_not_in_subscription = vec![5, 9, 8, 7];

		let provider = MockHeaderProvider(Arc::new(Mutex::new(heights_not_in_subscription.into())));
		let subscription = MockHeaderSubscription(heights_in_subscription.into());
		let mut headers = FinalizedHeaders::new(&provider, subscription);

		for h in all_heights {
			assert_eq!(h, headers.next().await.unwrap().number);
		}
		assert_eq!(None, headers.next().await);
	}
}
