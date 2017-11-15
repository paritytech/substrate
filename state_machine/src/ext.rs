// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Conrete externalities implementation.

use std::{error, fmt};

use backend::Backend;
use primitives::Address;
use primitives::contract::{CallData, OutData};
use primitives::hash::H256;
use {Externalities, CodeExecutor, StaticExternalities, OverlayedChanges};

/// Errors that can occur when interacting with the externalities.
#[derive(Debug, Copy, Clone)]
pub enum Error<B, E> {
	/// Failure to load state data from the backend.
	Backend(B),
	/// Failure to execute a function.
	Executor(E),
}

impl<B: fmt::Display, E: fmt::Display> fmt::Display for Error<B, E> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Error::Backend(ref e) => write!(f, "Storage backend error: {}", e),
			Error::Executor(ref e) => write!(f, "Sub-call execution error: {}", e),
		}
	}
}

impl<B: error::Error, E: error::Error> error::Error for Error<B, E> {
	fn description(&self) -> &str {
		match *self {
			Error::Backend(..) => "backend error",
			Error::Executor(..) => "executor error",
		}
	}
}

/// Wraps a read-only backend, call executor, and current overlayed changes.
pub struct Ext<'a, B: 'a, E: 'a> {
	/// The overlayed changes to write to.
	pub overlay: &'a mut OverlayedChanges,
	/// The storage backend to read from.
	pub backend: &'a B,
	/// Contract code executor.
	pub exec: &'a E,
	/// Contract address.
	pub local: Address,
}

impl<'a, B: 'a, E: 'a> StaticExternalities<E> for Ext<'a, B, E>
	where B: Backend, E: CodeExecutor
{
	type Error = Error<B::Error, E::Error>;

	fn storage(&self, key: &H256) -> Result<&[u8], Self::Error> {
		match self.overlay.storage(&self.local, key) {
			Some(x) => Ok(x),
			None => self.backend.storage(&self.local, key).map_err(Error::Backend)
		}
	}

	fn call_static(&self, address: &Address, method: &str, data: &CallData) -> Result<OutData, Self::Error> {
		let inner_ext = StaticExt {
			backend: self.backend,
			exec: self.exec,
			local: address.clone(),
			overlay: self.overlay,
		};

		let code = match self.overlay.code(address) {
			Some(x) => x,
			None => self.backend.code(address).map_err(Error::Backend)?,
		};

		self.exec.call_static(
			&inner_ext,
			code,
			method,
			data,
		).map_err(Error::Executor)
	}
}

impl<'a, B: 'a, E: 'a> Externalities<E> for Ext<'a, B, E>
	where B: Backend, E: CodeExecutor
{
	fn set_storage(&mut self, key: H256, value: Vec<u8>) {
		self.overlay.set_storage(self.local, key, value);
	}

	fn call(&mut self, address: &Address, method: &str, data: &CallData) -> Result<OutData, Self::Error> {
		let code = {
			let code = match self.overlay.code(address) {
				Some(x) => x,
				None => self.backend.code(address).map_err(Error::Backend)?,
			};

			code.to_owned()
		};

		let mut inner_ext = Ext {
			backend: self.backend,
			exec: self.exec,
			local: address.clone(),
			overlay: &mut *self.overlay,
		};

		self.exec.call(
			&mut inner_ext,
			&code[..],
			method,
			data,
		).map_err(Error::Executor)
	}
}

// Static externalities
struct StaticExt<'a, B: 'a, E: 'a> {
	overlay: &'a OverlayedChanges,
	backend: &'a B,
	exec: &'a E,
	local: Address,
}

impl<'a, B: 'a, E: 'a> StaticExternalities<E> for StaticExt<'a, B, E>
	where B: Backend, E: CodeExecutor
{
	type Error = Error<B::Error, E::Error>;

	fn storage(&self, key: &H256) -> Result<&[u8], Self::Error> {
		match self.overlay.storage(&self.local, key) {
			Some(x) => Ok(x),
			None => self.backend.storage(&self.local, key).map_err(Error::Backend)
		}
	}

	fn call_static(&self, address: &Address, method: &str, data: &CallData) -> Result<OutData, Self::Error> {
		let inner_ext = StaticExt {
			backend: self.backend,
			exec: self.exec,
			local: address.clone(),
			overlay: self.overlay,
		};

		let code = match self.overlay.code(address) {
			Some(x) => x,
			None => self.backend.code(address).map_err(Error::Backend)?,
		};

		self.exec.call_static(
			&inner_ext,
			code,
			method,
			data,
		).map_err(Error::Executor)
	}
}
