// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Generating request logic for request/response protocol for syncing BEEFY justifications.

use beefy_primitives::BeefyApi;
use codec::Encode;
use futures::{
	channel::{oneshot, oneshot::Canceled},
	future::Either,
	stream::{FuturesUnordered, StreamExt},
};
use log::{debug, error};
use sc_network::{PeerId, ProtocolName};
use sc_network_common::{
	request_responses::{IfDisconnected, RequestFailure},
	service::NetworkRequest,
};
use sp_api::ProvideRuntimeApi;
use sp_runtime::{
	generic::BlockId,
	traits::{Block, NumberFor},
};
use std::{result::Result, sync::Arc};

use crate::{
	communication::request_response::{Error, JustificationRequest},
	justification::{decode_and_verify_finality_proof, BeefyVersionedFinalityProof},
};

/// Response type received from network.
type Response = Result<Vec<u8>, RequestFailure>;
/// Used to receive a response from the network.
type ResponseReceiver = oneshot::Receiver<Response>;

enum State<B: Block> {
	Idle,
	AwaitingResponse(NumberFor<B>),
}

pub struct OnDemandJustificationsEngine<B: Block, N, R> {
	network: N,
	runtime: Arc<R>,
	protocol_name: ProtocolName,
	state: State<B>,
	engine: FuturesUnordered<
		Either<std::future::Pending<std::result::Result<Response, Canceled>>, ResponseReceiver>,
	>,
}

impl<B, N, R> OnDemandJustificationsEngine<B, N, R>
where
	B: Block,
	N: NetworkRequest,
	R: ProvideRuntimeApi<B>,
	R::Api: BeefyApi<B>,
{
	pub fn new(network: N, runtime: Arc<R>, protocol_name: ProtocolName) -> Self {
		let engine = FuturesUnordered::new();
		engine.push(Either::Left(std::future::pending::<_>()));
		Self { network, runtime, protocol_name, state: State::Idle, engine }
	}

	/// Start requesting justification for `block` number.
	pub fn request(&mut self, block: NumberFor<B>) {
		// TODO: do peer selection based on `known_peers`.
		let peer = PeerId::random();

		let payload = JustificationRequest::<B> { begin: block }.encode();

		let (tx, rx) = oneshot::channel();

		self.network.start_request(
			peer,
			self.protocol_name.clone(),
			payload,
			tx,
			IfDisconnected::ImmediateError,
		);

		self.engine.push(Either::Right(rx));
		self.state = State::AwaitingResponse(block);
	}

	pub async fn next(&mut self) -> Option<BeefyVersionedFinalityProof<B>> {
		// The `engine` contains at the very least a `Pending` future (future that never finishes).
		// This "blocks" until:
		//  - we have a [ResponseReceiver] added to the engine, and
		//  - we also get a [Response] on it.
		let resp = self.engine.next().await;

		let resp = resp.expect("Engine will never end because of inner `Pending` future, qed.");
		let number = match self.state {
			State::AwaitingResponse(block) => block,
			// Programming error to have active [ResponseReceiver]s in the engine with no pending
			// requests.
			State::Idle => {
				error!(
					target: "beefy",
					"🥩 unexpected response received: {:?}",
					resp
				);
				return None
			},
		};

		let resp = match resp {
			Ok(resp) => resp,
			Err(e) => {
				debug!(
					target: "beefy",
					"🥩 on demand justification (block {:?}) peer hung up: {:?}",
					number, e
				);
				self.request(number);
				return None
			},
		};

		let encoded = match resp {
			Ok(encoded) => encoded,
			Err(e) => {
				error!(
					target: "beefy",
					"🥩 on demand justification (block {:?}) peer responded with error: {:?}",
					number, e
				);
				return None
			},
		};

		match self.process_response(encoded, number) {
			Ok(proof) => Some(proof),
			Err(e) => {
				debug!(
					target: "beefy",
					"🥩 on demand justification (block {:?}) invalid proof: {:?}",
					number, e
				);
				self.request(number);
				None
			},
		}
	}

	fn process_response(
		&mut self,
		encoded: Vec<u8>,
		number: NumberFor<B>,
	) -> Result<BeefyVersionedFinalityProof<B>, Error> {
		let block_id = BlockId::number(number);
		let validator_set = self
			.runtime
			.runtime_api()
			.validator_set(&block_id)
			.map_err(Error::RuntimeApi)?
			.ok_or_else(|| Error::Pallet)?;

		let proof = decode_and_verify_finality_proof::<B>(&encoded[..], number, &validator_set);
		proof.map_err(|_| Error::TodoError)
	}

	/// Cancel any pending request for block numbers smaller or equal to `latest_block`.
	pub fn cancel_requests_older_than(&mut self, latest_block: NumberFor<B>) {
		match &self.state {
			State::AwaitingResponse(block) if *block <= latest_block => {
				debug!(
					target: "beefy",
					"🥩 cancel pending request for block: {:?}",
					block
				);
				self.state = State::Idle;
				self.engine = FuturesUnordered::new();
				self.engine.push(Either::Left(std::future::pending::<_>()));
			},
			_ => (),
		}
	}
}
