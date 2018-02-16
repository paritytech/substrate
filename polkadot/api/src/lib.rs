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

//! Strongly typed API for Polkadot based around the locally-compiled native
//! runtime.

extern crate polkadot_executor as polkadot_executor;
extern crate polkadot_runtime ;
extern crate polkadot_primitives as primitives;
extern crate substrate_client as client;
extern crate substrate_executor as substrate_executor;
extern crate substrate_state_machine as state_machine;

#[macro_use]
extern crate error_chain;

use client::backend::Backend;
use client::Client;
use polkadot_runtime::runtime;
use polkadot_executor::Executor as LocalDispatch;
use substrate_executor::{NativeExecutionDispatch, NativeExecutor};
use primitives::{AccountId, SessionKey};
use primitives::block::Id as BlockId;
use primitives::parachain::DutyRoster;

error_chain! {
	errors {
		/// Unknown runtime code.
		UnknownRuntime {
			description("Unknown runtime code")
			display("Unknown runtime code")
		}
		UnknownBlock(b: BlockId) {
			description("Unknown block")
			display("Unknown block")
		}
		/// Some other error.
		// TODO: allow to be specified as associated type of PolkadotApi
		Other(e: Box<::std::error::Error + Send>) {
			description("Other error")
			display("Other error: {}", e.description())
		}
	}

	links {
		Executor(substrate_executor::error::Error, substrate_executor::error::ErrorKind);
	}
}

/// Trait encapsulating the Polkadot API.
///
/// All calls should fail when the exact runtime is unknown.
pub trait PolkadotApi {
	/// Get session keys at a given block.
	fn session_keys(&self, at: &BlockId) -> Result<Vec<SessionKey>>;

	/// Get validators at a given block.
	fn validators(&self, at: &BlockId) -> Result<Vec<AccountId>>;

	/// Get the authority duty roster at a block.
	fn duty_roster(&self, at: &BlockId) -> Result<DutyRoster>;
}

fn convert_client_error(e: client::error::Error) -> Error {
	match e {
		client::error::Error(client::error::ErrorKind::UnknownBlock(b), _) => Error::from_kind(ErrorKind::UnknownBlock(b)),
		other => Error::from_kind(ErrorKind::Other(Box::new(other) as Box<_>)),
	}
}

// set up the necessary scaffolding to execute the runtime.
macro_rules! with_runtime {
	($client: ident, $at: expr, $exec: expr) => {{
		// bail if the code is not the same as the natively linked.
		if $client.code_at($at).map_err(convert_client_error)? != LocalDispatch::native_equivalent() {
			bail!(ErrorKind::UnknownRuntime);
		}

		$client.state_at($at).map_err(convert_client_error).and_then(|state| {
			let mut changes = Default::default();
			let mut ext = state_machine::Ext {
				overlay: &mut changes,
				backend: &state,
			};

			::substrate_executor::with_native_environment(&mut ext, $exec).map_err(Into::into)
		})
	}}
}

impl<B: Backend> PolkadotApi for Client<B, NativeExecutor<LocalDispatch>>
	where ::client::error::Error: From<<<B as Backend>::State as state_machine::backend::Backend>::Error>
{
	fn session_keys(&self, at: &BlockId) -> Result<Vec<SessionKey>> {
		with_runtime!(self, at, ::runtime::consensus::authorities)
	}

	fn validators(&self, at: &BlockId) -> Result<Vec<AccountId>> {
		with_runtime!(self, at, ::runtime::session::validators)
	}

	fn duty_roster(&self, at: &BlockId) -> Result<DutyRoster> {
		with_runtime!(self, at, ::runtime::parachains::calculate_duty_roster)
	}
}
