// This file is part of Substrate.

// Copyright (C) 2017-2023 Parity Technologies (UK) Ltd.
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

use std::{
	sync::{
		atomic::{AtomicBool, Ordering},
		Arc,
	},
	time::Duration,
};

/// An error signifying that a task has been cancelled due to a timeout.
#[derive(Debug)]
pub struct Timeout;

impl std::error::Error for Timeout {}
impl std::fmt::Display for Timeout {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		fmt.write_str("task has been running too long")
	}
}

/// A handle which can be used to check whether the task has been cancelled due to a timeout.
#[repr(transparent)]
pub struct IsTimedOut(Arc<AtomicBool>);

impl IsTimedOut {
	#[must_use]
	pub fn check_if_timed_out(&self) -> std::result::Result<(), Timeout> {
		if self.0.load(Ordering::Relaxed) {
			Err(Timeout)
		} else {
			Ok(())
		}
	}
}

/// An error for a task which either panicked, or has been cancelled due to a timeout.
#[derive(Debug)]
pub enum SpawnWithTimeoutError {
	JoinError(tokio::task::JoinError),
	Timeout,
}

impl std::error::Error for SpawnWithTimeoutError {}
impl std::fmt::Display for SpawnWithTimeoutError {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		match self {
			SpawnWithTimeoutError::JoinError(error) => error.fmt(fmt),
			SpawnWithTimeoutError::Timeout => Timeout.fmt(fmt),
		}
	}
}

struct CancelOnDrop(Arc<AtomicBool>);
impl Drop for CancelOnDrop {
	fn drop(&mut self) {
		self.0.store(true, Ordering::Relaxed)
	}
}

/// Spawns a new blocking task with a given `timeout`.
///
/// The `callback` should continuously call [`IsTimedOut::check_if_timed_out`],
/// which will return an error once the task runs for longer than `timeout`.
///
/// If `timeout` is `None` then this works just as a regular `spawn_blocking`.
pub async fn spawn_blocking_with_timeout<R>(
	timeout: Option<Duration>,
	callback: impl FnOnce(IsTimedOut) -> std::result::Result<R, Timeout> + Send + 'static,
) -> Result<R, SpawnWithTimeoutError>
where
	R: Send + 'static,
{
	let is_timed_out_arc = Arc::new(AtomicBool::new(false));
	let is_timed_out = IsTimedOut(is_timed_out_arc.clone());
	let _cancel_on_drop = CancelOnDrop(is_timed_out_arc);
	let task = tokio::task::spawn_blocking(move || callback(is_timed_out));

	let result = if let Some(timeout) = timeout {
		tokio::select! {
			// Shouldn't really matter, but make sure the task is polled before the timeout,
			// in case the task finishes after the timeout and the timeout is really short.
			biased;

			task_result = task => task_result,
			_ = tokio::time::sleep(timeout) => Ok(Err(Timeout))
		}
	} else {
		task.await
	};

	match result {
		Ok(Ok(result)) => Ok(result),
		Ok(Err(Timeout)) => Err(SpawnWithTimeoutError::Timeout),
		Err(error) => Err(SpawnWithTimeoutError::JoinError(error)),
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[tokio::test]
	async fn spawn_blocking_with_timeout_works() {
		let task: Result<(), SpawnWithTimeoutError> =
			spawn_blocking_with_timeout(Some(Duration::from_millis(100)), |is_timed_out| {
				std::thread::sleep(Duration::from_millis(200));
				is_timed_out.check_if_timed_out()?;
				unreachable!();
			})
			.await;

		assert_matches::assert_matches!(task, Err(SpawnWithTimeoutError::Timeout));

		let task = spawn_blocking_with_timeout(Some(Duration::from_millis(100)), |is_timed_out| {
			std::thread::sleep(Duration::from_millis(20));
			is_timed_out.check_if_timed_out()?;
			Ok(())
		})
		.await;

		assert_matches::assert_matches!(task, Ok(()));
	}
}
