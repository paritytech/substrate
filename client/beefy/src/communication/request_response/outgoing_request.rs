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

use codec::{Decode, Encode};
use futures::{channel::oneshot, stream::FusedStream, FutureExt, Stream};
use sc_network::PeerId;
use sc_network_common::{
	request_responses::{IfDisconnected, RequestFailure},
	service::NetworkRequest,
};
use sp_runtime::traits::{Block, NumberFor};
use std::{
	pin::Pin,
	task::{Context, Poll, Waker},
};

use crate::{
	communication::request_response::JustificationRequest,
	justification::BeefyVersionedFinalityProof,
};

/// Used to receive a response from the network.
type ResponseReceiver = oneshot::Receiver<std::result::Result<Vec<u8>, RequestFailure>>;

enum State<B: Block> {
	Init,
	Idle(Waker),
	AwaitingResponse(NumberFor<B>, ResponseReceiver),
}

pub struct OnDemandJustififactionsEngine<B: Block, N> {
	network: N,
	protocol_name: std::borrow::Cow<'static, str>,
	state: State<B>,
}

impl<B, N> OnDemandJustififactionsEngine<B, N>
where
	B: Block,
	N: NetworkRequest,
{
	pub fn new(network: N, protocol_name: std::borrow::Cow<'static, str>) -> Self {
		Self { network, protocol_name, state: State::Init }
	}

	pub fn fire_request_for(&mut self, block: NumberFor<B>) {
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

		self.state = State::AwaitingResponse(block, rx);
	}

	/// Cancel any pending request for block numbers smaller or equal to `latest_block`.
	pub fn cancel_requests_older_than(&mut self, latest_block: NumberFor<B>) {
		match &self.state {
			State::Init | State::Idle(_) => (),
			State::AwaitingResponse(block, _) if *block <= latest_block => {
				// TODO: this should be `State::Idle` but I need to figure out if I need that
				// `Waker` or not.
				self.state = State::Init;
			},
			_ => (),
		}
	}
}

impl<B, N> Stream for OnDemandJustififactionsEngine<B, N>
where
	B: Block,
	N: NetworkRequest,
{
	type Item = BeefyVersionedFinalityProof<B>;

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
		// TODO: I don't think we need this waker, should remove.
		let waker = cx.waker().clone();

		let response_receiver = match &mut self.state {
			// If there's nothing to do,
			State::Init | State::Idle(_) => {
				self.state = State::Idle(waker);
				// do nothing.
				return Poll::Pending
			},
			State::AwaitingResponse(_block, receiver) => receiver,
		};

		match response_receiver.poll_unpin(cx) {
			Poll::Ready(Ok(Ok(encoded))) => {
				self.state = State::Idle(waker);

				match <BeefyVersionedFinalityProof<B>>::decode(&mut &*encoded) {
					// TODO: Verify this proof is valid.
					Ok(proof) => return Poll::Ready(Some(proof)),
					Err(_) => {
						// TODO: decode error, try another peer.
					},
				}
			},
			Poll::Ready(Err(_)) | Poll::Ready(Ok(Err(_))) => {
				self.state = State::Idle(waker);
				// TODO: this peer closed connection or couldn't/refused to answer, try another.
			},
			Poll::Pending => (),
		}

		Poll::Pending
	}
}

impl<B, N> FusedStream for OnDemandJustififactionsEngine<B, N>
where
	B: Block,
	N: NetworkRequest,
{
	fn is_terminated(&self) -> bool {
		false
	}
}

impl<B, N> Unpin for OnDemandJustififactionsEngine<B, N>
where
	B: Block,
	N: NetworkRequest,
{
}
