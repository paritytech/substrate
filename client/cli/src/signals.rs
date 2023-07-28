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

use futures::{
	future::{self, BoxFuture, FutureExt},
	pin_mut, select, Future,
};

use sc_service::Error as ServiceError;

/// Abstraction over OS signals to handle the shutdown of the node smoothly.
///
/// On `unix` this represents `SigInt` and `SigTerm`.
pub struct Signals(BoxFuture<'static, ()>);

impl Signals {
	/// Return the signals future.
	pub fn future(self) -> BoxFuture<'static, ()> {
		self.0
	}

	/// Capture the relevant signals to handle shutdown of the node smoothly.
	///
	/// Needs to be called in a Tokio context to have access to the tokio reactor.
	#[cfg(target_family = "unix")]
	pub fn capture() -> std::result::Result<Self, ServiceError> {
		use tokio::signal::unix::{signal, SignalKind};

		let mut stream_int = signal(SignalKind::interrupt()).map_err(ServiceError::Io)?;
		let mut stream_term = signal(SignalKind::terminate()).map_err(ServiceError::Io)?;

		Ok(Signals(
			async move {
				future::select(stream_int.recv().boxed(), stream_term.recv().boxed()).await;
			}
			.boxed(),
		))
	}

	/// Capture the relevant signals to handle shutdown of the node smoothly.
	///
	/// Needs to be called in a Tokio context to have access to the tokio reactor.
	#[cfg(not(unix))]
	pub fn capture() -> Result<Self, ServiceError> {
		use tokio::signal::ctrl_c;

		Ok(Signals(
			async move {
				let _ = ctrl_c().await;
			}
			.boxed(),
		))
	}

	/// A dummy signal that never returns.
	pub fn dummy() -> Self {
		Self(future::pending().boxed())
	}

	/// Run a future task until receive a signal.
	pub async fn run_until_signal<F, E>(self, func: F) -> Result<(), E>
	where
		F: Future<Output = Result<(), E>> + future::FusedFuture,
		E: std::error::Error + Send + Sync + 'static,
	{
		let signals = self.future().fuse();

		pin_mut!(func, signals);

		select! {
			_ = signals => {},
			res = func => res?,
		}

		Ok(())
	}
}
