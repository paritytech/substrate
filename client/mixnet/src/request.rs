// This file is part of Substrate.

// Copyright (C) 2022-2023 Parity Technologies (UK) Ltd.
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

//! Sender-side request logic. Some things from this module are also used on the receiver side, eg
//! [`extrinsic_delay`], but most of the receiver-side request logic lives elsewhere.

use super::{config::SubstrateConfig, error::Error};
use blake2::{
	digest::{consts::U16, Mac},
	Blake2bMac,
};
use codec::{Decode, DecodeAll};
use futures::channel::oneshot;
use log::warn;
use mixnet::core::{Delay, MessageId, PostErr, Scattered};
use sp_core::Bytes;
use std::time::Duration;

const LOG_TARGET: &str = "mixnet";

fn send_err<T>(reply_sender: oneshot::Sender<Result<T, Error>>, err: Error) {
	if let Err(Err(err)) = reply_sender.send(Err(err)) {
		warn!(target: LOG_TARGET, "Failed to inform requester of error: {err}");
	}
}

fn send_reply<T: Decode>(reply_sender: oneshot::Sender<Result<T, Error>>, mut data: &[u8]) {
	let res = match Result::decode_all(&mut data) {
		Ok(res) => res.map_err(Error::Remote),
		Err(_) => Err(Error::BadReply),
	};
	match reply_sender.send(res) {
		Ok(_) => (),
		Err(Ok(_)) => warn!(target: LOG_TARGET, "Failed to send reply to requester"),
		Err(Err(err)) => warn!(target: LOG_TARGET, "Failed to inform requester of error: {err}"),
	}
}

pub const SUBMIT_EXTRINSIC: u8 = 1;

const EXTRINSIC_DELAY_PERSONA: &[u8; 16] = b"submit-extrn-dly";

pub fn extrinsic_delay(message_id: &MessageId, config: &SubstrateConfig) -> Duration {
	let h = Blake2bMac::<U16>::new_with_salt_and_personal(message_id, b"", EXTRINSIC_DELAY_PERSONA)
		.expect("Key, salt, and persona sizes are fixed and small enough");
	let delay = Delay::exp(h.finalize().into_bytes().as_ref());
	delay.to_duration(config.mean_extrinsic_delay)
}

pub enum Request {
	SubmitExtrinsic { extrinsic: Bytes, reply_sender: oneshot::Sender<Result<(), Error>> },
}

impl Request {
	fn send_err(self, err: Error) {
		match self {
			Request::SubmitExtrinsic { reply_sender, .. } => send_err(reply_sender, err),
		}
	}

	pub fn send_reply(self, data: &[u8]) {
		match self {
			Request::SubmitExtrinsic { reply_sender, .. } => send_reply(reply_sender, data),
		}
	}
}

impl mixnet::request_manager::Request for Request {
	type Context = SubstrateConfig;

	fn with_data<T>(&self, f: impl FnOnce(Scattered<u8>) -> T, _context: &Self::Context) -> T {
		match self {
			Request::SubmitExtrinsic { extrinsic, .. } =>
				f([&[SUBMIT_EXTRINSIC], extrinsic.as_ref()].as_slice().into()),
		}
	}

	fn num_surbs(&self, context: &Self::Context) -> usize {
		match self {
			Request::SubmitExtrinsic { .. } => context.surb_factor,
		}
	}

	fn handling_delay(&self, message_id: &MessageId, context: &Self::Context) -> Duration {
		match self {
			Request::SubmitExtrinsic { .. } => extrinsic_delay(message_id, context),
		}
	}

	fn handle_post_err(self, err: PostErr, _context: &Self::Context) {
		self.send_err(err.into());
	}

	fn handle_retry_limit_reached(self, _context: &Self::Context) {
		self.send_err(Error::NoReply);
	}
}
