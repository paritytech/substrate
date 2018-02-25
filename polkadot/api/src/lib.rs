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
extern crate polkadot_runtime;
extern crate polkadot_primitives as primitives;
extern crate substrate_client as client;
extern crate substrate_executor as substrate_executor;
extern crate substrate_state_machine as state_machine;

#[macro_use]
extern crate error_chain;

#[cfg(test)]
extern crate substrate_keyring as keyring;

use client::backend::Backend;
use client::Client;
use polkadot_runtime::runtime;
use polkadot_executor::Executor as LocalDispatch;
use substrate_executor::{NativeExecutionDispatch, NativeExecutor};
use state_machine::OverlayedChanges;
use primitives::{AccountId, SessionKey, Timestamp};
use primitives::block::{Id as BlockId, Block, Header, Body};
use primitives::transaction::UncheckedTransaction;
use primitives::parachain::DutyRoster;

error_chain! {
	errors {
		/// Unknown runtime code.
		UnknownRuntime {
			description("Unknown runtime code")
			display("Unknown runtime code")
		}
		/// Unknown block ID.
		UnknownBlock(b: BlockId) {
			description("Unknown block")
			display("Unknown block")
		}
		/// Attempted to push an inherent transaction manually.
		PushedInherentTransaction(tx: UncheckedTransaction) {
			description("Attempted to push an inherent transaction to a block."),
			display("Pushed inherent transaction to a block: {:?}", tx),
		}
		/// Badly-formed transaction.
		BadlyFormedTransaction(tx: UncheckedTransaction) {
			description("Attempted to push a badly-formed transaction to a block."),
			display("Pushed badly-formed transaction to a block: {:?}", tx),
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

impl From<client::error::Error> for Error {
	fn from(e: client::error::Error) -> Error {
		match e {
			client::error::Error(client::error::ErrorKind::UnknownBlock(b), _) => Error::from_kind(ErrorKind::UnknownBlock(b)),
			other => Error::from_kind(ErrorKind::Other(Box::new(other) as Box<_>)),
		}
	}
}

pub trait BlockBuilder: Sized {
	/// Push a non-inherent transaction.
	fn push_transaction(&mut self, transaction: UncheckedTransaction) -> Result<()>;

	/// Finalise the block.
	fn bake(self) -> Block;
}

/// Trait encapsulating the Polkadot API.
///
/// All calls should fail when the exact runtime is unknown.
pub trait PolkadotApi {
	type BlockBuilder: BlockBuilder;

	/// Get session keys at a given block.
	fn session_keys(&self, at: &BlockId) -> Result<Vec<SessionKey>>;

	/// Get validators at a given block.
	fn validators(&self, at: &BlockId) -> Result<Vec<AccountId>>;

	/// Get the authority duty roster at a block.
	fn duty_roster(&self, at: &BlockId) -> Result<DutyRoster>;

	/// Get the timestamp registered at a block.
	fn timestamp(&self, at: &BlockId) -> Result<Timestamp>;

	/// Evaluate a block and see if it gives an error.
	fn evaluate_block(&self, at: &BlockId, block: Block) -> Result<()>;

	/// Create a block builder on top of the parent block.
	fn build_block(&self, parent: &BlockId, timestamp: u64) -> Result<Self::BlockBuilder>;
}

// set up the necessary scaffolding to execute the runtime.
macro_rules! with_runtime {
	($client: ident, $at: expr, $exec: expr) => {{
		// bail if the code is not the same as the natively linked.
		if $client.code_at($at)? != LocalDispatch::native_equivalent() {
			bail!(ErrorKind::UnknownRuntime);
		}

		$client.state_at($at).map_err(Error::from).and_then(|state| {
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
	type BlockBuilder = ClientBlockBuilder<B::State>;

	fn session_keys(&self, at: &BlockId) -> Result<Vec<SessionKey>> {
		with_runtime!(self, at, ::runtime::consensus::authorities)
	}

	fn validators(&self, at: &BlockId) -> Result<Vec<AccountId>> {
		with_runtime!(self, at, ::runtime::session::validators)
	}

	fn duty_roster(&self, at: &BlockId) -> Result<DutyRoster> {
		with_runtime!(self, at, ::runtime::parachains::calculate_duty_roster)
	}

	fn timestamp(&self, at: &BlockId) -> Result<Timestamp> {
		with_runtime!(self, at, ::runtime::timestamp::get)
	}

	fn evaluate_block(&self, at: &BlockId, block: Block) -> Result<()> {
		with_runtime!(self, at, || ::runtime::system::internal::execute_block(block))
	}

	fn build_block(&self, parent: &BlockId, timestamp: Timestamp) -> Result<Self::BlockBuilder> {
		if self.code_at(parent)? != LocalDispatch::native_equivalent() {
			bail!(ErrorKind::UnknownRuntime);
		}

		let header = Header {
			parent_hash: self.block_hash_from_id(parent)?.ok_or(ErrorKind::UnknownBlock(*parent))?,
			number: self.block_number_from_id(parent)?.ok_or(ErrorKind::UnknownBlock(*parent))? + 1,
			state_root: Default::default(),
			transaction_root: Default::default(),
			digest: Default::default(),
		};

		let body = Body {
			timestamp: timestamp,
			transactions: Vec::new(),
		};

		let mut builder = ClientBlockBuilder {
			parent: *parent,
			changes: OverlayedChanges::default(),
			state: self.state_at(parent)?,
			header,
			timestamp,
			transactions: Vec::new(),
		};

		for inherent in body.inherent_transactions() {
			builder.execute_transaction(inherent)?;
		}

		Ok(builder)
	}
}

/// A polkadot block builder.
#[derive(Debug, Clone)]
pub struct ClientBlockBuilder<S> {
	parent: BlockId,
	changes: OverlayedChanges,
	state: S,
	header: Header,
	timestamp: Timestamp,
	transactions: Vec<UncheckedTransaction>,
}

impl<S: state_machine::Backend> ClientBlockBuilder<S>
	where S::Error: Into<client::error::Error>
{
	// executes a transaction, inherent or otherwise, without appending to the list
	fn execute_transaction(&mut self, transaction: UncheckedTransaction) -> Result<()> {
		if !transaction.is_well_formed() {
			bail!(ErrorKind::BadlyFormedTransaction(transaction));
		}

		let mut ext = state_machine::Ext {
			overlay: &mut self.changes,
			backend: &self.state,
		};

		// TODO: avoid clone
		let header = self.header.clone();
		let result = ::substrate_executor::with_native_environment(
			&mut ext,
			move || runtime::system::internal::execute_transaction(transaction, header),
		).map_err(Into::into);

		match result {
			Ok(header) => {
				ext.overlay.commit_prospective();
				self.header = header;
				Ok(())
			}
			Err(e) => {
				ext.overlay.discard_prospective();
				Err(e)
			}
		}
	}
}

impl<S: state_machine::Backend> BlockBuilder for ClientBlockBuilder<S>
	where S::Error: Into<client::error::Error>
{
	fn push_transaction(&mut self, transaction: UncheckedTransaction) -> Result<()> {
		if transaction.transaction.function.is_inherent() {
			bail!(ErrorKind::PushedInherentTransaction(transaction));
		} else {
			self.execute_transaction(transaction.clone())?;
			self.transactions.push(transaction);
			Ok(())
		}
	}

	fn bake(mut self) -> Block {
		let mut ext = state_machine::Ext {
			overlay: &mut self.changes,
			backend: &self.state,
		};

		let old_header = self.header;
		let final_header = ::substrate_executor::with_native_environment(
			&mut ext,
			move || runtime::system::internal::finalise_block(old_header)
		).expect("all inherent transactions pushed; all other transactions executed correctly; qed");

		Block {
			header: final_header,
			body: Body {
				timestamp: self.timestamp,
				transactions: self.transactions,
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use client::in_mem::Backend as InMemory;
	use polkadot_runtime::genesismap::{additional_storage_with_genesis, GenesisConfig};
	use substrate_executor::NativeExecutionDispatch;
	use keyring::Keyring;

	fn validators() -> Vec<AccountId> {
		vec![
			Keyring::One.to_raw_public(),
			Keyring::Two.to_raw_public(),
		]
	}

	fn client() -> Client<InMemory, NativeExecutor<LocalDispatch>> {
		::client::new_in_mem(
			LocalDispatch::new(),
			|| {
				let config = GenesisConfig::new_simple(validators(), 100);

				// override code entry.
				let mut storage = config.genesis_map();
				storage.insert(b":code".to_vec(), LocalDispatch::native_equivalent().to_vec());

				let block = ::client::genesis::construct_genesis_block(
					&config.genesis_map()
				);
				storage.extend(additional_storage_with_genesis(&block));
				(block.header, storage.into_iter().collect())
			}
		).unwrap()
	}

	#[test]
	fn gets_session_and_validator_keys() {
		let client = client();
		assert_eq!(client.session_keys(&BlockId::Number(0)).unwrap(), validators());
		assert_eq!(client.validators(&BlockId::Number(0)).unwrap(), validators());
	}

	#[test]
	fn build_block() {
		let client = client();

		let block_builder = client.build_block(&BlockId::Number(0), 1_000_000).unwrap();
		let block = block_builder.bake();

		assert_eq!(block.header.number, 1);
	}

	#[test]
	fn cannot_build_block_on_unknown_parent() {
		let client = client();
		assert!(client.build_block(&BlockId::Number(100), 1_000_000).is_err());
	}
}
