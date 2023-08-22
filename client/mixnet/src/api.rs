// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use super::{config::Config, error::Error, request::Request};
use futures::{
	channel::{mpsc, oneshot},
	SinkExt,
};
use sp_core::Bytes;
use std::future::Future;

/// The other end of an [`Api`]. This should be passed to [`run`](super::run::run).
pub struct ApiBackend {
	pub(super) request_receiver: mpsc::Receiver<Request>,
}

/// Interface to the mixnet service.
#[derive(Clone)]
pub struct Api {
	request_sender: mpsc::Sender<Request>,
}

impl Api {
	/// Create a new `Api`. The [`ApiBackend`] should be passed to [`run`](super::run::run).
	pub fn new(config: &Config) -> (Self, ApiBackend) {
		let (request_sender, request_receiver) = mpsc::channel(config.substrate.request_buffer);
		(Self { request_sender }, ApiBackend { request_receiver })
	}

	/// Submit an extrinsic via the mixnet.
	///
	/// Returns a [`Future`] which returns another `Future`.
	///
	/// The first `Future` resolves as soon as there is space in the mixnet service queue. The
	/// second `Future` resolves once a reply is received over the mixnet (or sooner if there is an
	/// error).
	///
	/// The first `Future` references `self`, but the second does not. This makes it possible to
	/// submit concurrent mixnet requests using a single `Api` instance.
	pub async fn submit_extrinsic(
		&mut self,
		extrinsic: Bytes,
	) -> impl Future<Output = Result<(), Error>> {
		let (reply_sender, reply_receiver) = oneshot::channel();
		let res = self
			.request_sender
			.feed(Request::SubmitExtrinsic { extrinsic, reply_sender })
			.await;
		async move {
			res.map_err(|_| Error::ServiceUnavailable)?;
			reply_receiver.await.map_err(|_| Error::ServiceUnavailable)?
		}
	}
}
