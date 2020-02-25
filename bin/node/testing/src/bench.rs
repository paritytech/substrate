// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Benchmarking module.
//!
//! Utilities to do full-scale benchmarks involving database. With `BenchDb` you
//! can pregenerate seed database and `clone` it for every iteration of your benchmarks
//! or tests to get consistent, smooth benchmark experience!

use std::{sync::Arc, path::Path, collections::BTreeMap};

use node_primitives::Block;
use crate::client::{Client, Backend};
use crate::keyring::*;
use sc_client_db::PruningMode;
use sc_executor::{NativeExecutor, WasmExecutionMethod};
use sp_consensus::{
	BlockOrigin, BlockImport, BlockImportParams,
	ForkChoiceStrategy, ImportResult, ImportedAux
};
use sp_runtime::{
	generic::BlockId,
	OpaqueExtrinsic,
	traits::{Block as BlockT, Verify, Zero, IdentifyAccount},
};
use codec::{Decode, Encode};
use node_runtime::{
	Call,
	CheckedExtrinsic,
	constants::currency::DOLLARS,
	UncheckedExtrinsic,
	MinimumPeriod,
	BalancesCall,
	AccountId,
	Signature,
};
use sp_core::ExecutionContext;
use sp_api::ProvideRuntimeApi;
use sp_block_builder::BlockBuilder;
use sp_inherents::InherentData;
use sc_client_api::{
	ExecutionStrategy,
	execution_extensions::{ExecutionExtensions, ExecutionStrategies},
};
use sp_core::{Pair, Public, sr25519};

/// Keyring full of accounts for benching.
///
/// Accounts are ordered:
///     //endowed-user//00
///     //endowed-user//01
///      ...
///     //endowed-user//N
#[derive(Clone)]
pub struct BenchKeyring {
	accounts: BTreeMap<AccountId, sr25519::Pair>,
}

/// Pre-initialized benchmarking database.
///
/// This is prepared database with genesis and keyring
/// that can be cloned and then used for any benchmarking.
pub struct BenchDb {
	keyring: BenchKeyring,
	directory_guard: Guard,
}

impl Clone for BenchDb {
	fn clone(&self) -> Self {
		let keyring = self.keyring.clone();
		let dir = tempfile::tempdir().expect("temp dir creation failed");

		let seed_dir = self.directory_guard.0.path();

		log::trace!(
			target: "bench-logistics",
			"Copying seed db from {} to {}",
			seed_dir.to_string_lossy(),
			dir.path().to_string_lossy(),
		);
		let seed_db_files = std::fs::read_dir(seed_dir)
			.expect("failed to list file in seed dir")
			.map(|f_result|
				f_result.expect("failed to read file in seed db")
					.path()
					.clone()
			).collect();
		fs_extra::copy_items(
			&seed_db_files,
			dir.path(),
			&fs_extra::dir::CopyOptions::new(),
		).expect("Copy of seed database is ok");

		BenchDb { keyring, directory_guard: Guard(dir) }
	}
}

impl BenchDb {
	/// New immutable benchmarking database.
	///
	/// This will generate database files in random temporary directory
	/// and keep it there until struct is dropped.
	///
	/// You can `clone` this database or you can `create_context` from it
	/// (which also do `clone`) to run actual operation against new database
	/// which will be identical to this.
	pub fn new(keyring_length: usize) -> Self {
		let keyring = BenchKeyring::new(keyring_length);

		let dir = tempfile::tempdir().expect("temp dir creation failed");
		log::trace!(
			target: "bench-logistics",
			"Created seed db at {}",
			dir.path().to_string_lossy(),
		);
		let (_client, _backend) = Self::bench_client(dir.path(), Profile::Native, &keyring);
		let directory_guard = Guard(dir);

		BenchDb { keyring, directory_guard }
	}

	// This should return client that is doing everything that full node
	// is doing.
	//
	// - This client should use best wasm execution method.
	// - This client should work with real database only.
	fn bench_client(dir: &std::path::Path, profile: Profile, keyring: &BenchKeyring) -> (Client, std::sync::Arc<Backend>) {
		let db_config = sc_client_db::DatabaseSettings {
			state_cache_size: 16*1024*1024,
			state_cache_child_ratio: Some((0, 100)),
			pruning: PruningMode::ArchiveAll,
			source: sc_client_db::DatabaseSettingsSrc::Path {
				path: dir.into(),
				cache_size: None,
			},
		};

		let (client, backend) = sc_client_db::new_client(
			db_config,
			NativeExecutor::new(WasmExecutionMethod::Compiled, None),
			&keyring.generate_genesis(),
			None,
			None,
			ExecutionExtensions::new(profile.into_execution_strategies(), None),
		).expect("Should not fail");

		(client, backend)
	}

	/// Generate new block using this database.
	pub fn generate_block(&mut self, transactions: usize) -> Block {
		let (client, _backend) = Self::bench_client(
			self.directory_guard.path(),
			Profile::Wasm,
			&self.keyring,
		);

		let version = client.runtime_version_at(&BlockId::number(0))
			.expect("There should be runtime version at 0")
			.spec_version;

		let genesis_hash = client.block_hash(Zero::zero())
			.expect("Database error?")
			.expect("Genesis block always exists; qed")
			.into();

		let mut block = client
			.new_block(Default::default())
			.expect("Block creation failed");

		let timestamp = 1 * MinimumPeriod::get();

		let mut inherent_data = InherentData::new();
		inherent_data.put_data(sp_timestamp::INHERENT_IDENTIFIER, &timestamp)
			.expect("Put timestamp failed");
		inherent_data.put_data(sp_finality_tracker::INHERENT_IDENTIFIER, &0)
			.expect("Put finality tracker failed");

		for extrinsic in client.runtime_api()
			.inherent_extrinsics_with_context(
				&BlockId::number(0),
				ExecutionContext::BlockConstruction,
				inherent_data,
			).expect("Get inherents failed")
		{
			block.push(extrinsic).expect("Push inherent failed");
		}

		let mut iteration = 0;
		let start = std::time::Instant::now();
		for _ in 0..transactions {

			let sender = self.keyring.at(iteration);
			let receiver = get_account_id_from_seed::<sr25519::Public>(
				&format!("random-user//{}", iteration)
			);

			let signed = self.keyring.sign(
				CheckedExtrinsic {
					signed: Some((sender, signed_extra(0, 1*DOLLARS))),
					function: Call::Balances(
						BalancesCall::transfer(
							pallet_indices::address::Address::Id(receiver),
							1*DOLLARS
						)
					),
				},
				version,
				genesis_hash,
			);

			let encoded = Encode::encode(&signed);

			let opaque = OpaqueExtrinsic::decode(&mut &encoded[..])
				.expect("Failed  to decode opaque");

			match block.push(opaque) {
				Err(sp_blockchain::Error::ApplyExtrinsicFailed(
						sp_blockchain::ApplyExtrinsicFailed::Validity(e)
				)) if e.exhausted_resources() => {
					break;
				},
				Err(err) => panic!("Error pushing transaction: {:?}", err),
				Ok(_) => {},
			}
			iteration += 1;
		}
		let block = block.build().expect("Block build failed").block;

		log::info!(
			target: "bench-logistics",
			"Block construction: {:#?} ({} tx)",
			start.elapsed(), block.extrinsics.len()
		);

		block
	}

	/// Database path.
	pub fn path(&self) -> &Path {
		self.directory_guard.path()
	}

	/// Clone this database and create context for testing/benchmarking.
	pub fn create_context(&self, profile: Profile) -> BenchContext {
		let BenchDb { directory_guard, keyring } = self.clone();
		let (client, backend) = Self::bench_client(directory_guard.path(), profile, &keyring);

		BenchContext {
			client, backend, db_guard: directory_guard,
		}
	}
}

impl BenchKeyring {
	/// New keyring.
	///
	/// `length` is the number of accounts generated.
	pub fn new(length: usize) -> Self {
		let mut accounts = BTreeMap::new();

		for n in 0..length {
			let seed = format!("//endowed-user/{}", n);
			let pair = sr25519::Pair::from_string(&seed, None).expect("failed to generate pair");
			let account_id = AccountPublic::from(pair.public()).into_account();
			accounts.insert(account_id, pair);
		}

		Self { accounts }
	}

	/// Generated account id-s from keyring keypairs.
	pub fn collect_account_ids(&self) -> Vec<AccountId> {
		self.accounts.keys().cloned().collect()
	}

	/// Get account id at position `index`
	pub fn at(&self, index: usize) -> AccountId {
		self.accounts.keys().nth(index).expect("Failed to get account").clone()
	}

	/// Sign transaction with keypair from this keyring.
	pub fn sign(&self, xt: CheckedExtrinsic, version: u32, genesis_hash: [u8; 32]) -> UncheckedExtrinsic {
		match xt.signed {
			Some((signed, extra)) => {
				let payload = (xt.function, extra.clone(), version, genesis_hash, genesis_hash);
				let key = self.accounts.get(&signed).expect("Account id not found in keyring");
				let signature = payload.using_encoded(|b| {
					if b.len() > 256 {
						key.sign(&sp_io::hashing::blake2_256(b))
					} else {
						key.sign(b)
					}
				}).into();
				UncheckedExtrinsic {
					signature: Some((pallet_indices::address::Address::Id(signed), signature, extra)),
					function: payload.0,
				}
			}
			None => UncheckedExtrinsic {
				signature: None,
				function: xt.function,
			},
		}
	}

	/// Generate genesis with accounts from this keyring endowed with some balance.
	pub fn generate_genesis(&self) -> node_runtime::GenesisConfig {
		crate::genesis::config_endowed(
			false,
			Some(node_runtime::WASM_BINARY),
			self.collect_account_ids(),
		)
	}
}

/// Profile for exetion strategies.
#[derive(Clone, Copy, Debug)]
pub enum Profile {
	/// As native as possible.
	Native,
	/// As wasm as possible.
	Wasm,
}

impl Profile {
	fn into_execution_strategies(self) -> ExecutionStrategies {
		match self {
			Profile::Wasm => ExecutionStrategies {
				syncing: ExecutionStrategy::AlwaysWasm,
				importing: ExecutionStrategy::AlwaysWasm,
				block_construction: ExecutionStrategy::AlwaysWasm,
				offchain_worker: ExecutionStrategy::AlwaysWasm,
				other: ExecutionStrategy::AlwaysWasm,
			},
			Profile::Native => ExecutionStrategies {
				syncing: ExecutionStrategy::NativeElseWasm,
				importing: ExecutionStrategy::NativeElseWasm,
				block_construction: ExecutionStrategy::NativeElseWasm,
				offchain_worker: ExecutionStrategy::NativeElseWasm,
				other: ExecutionStrategy::NativeElseWasm,
			}
		}
	}
}

struct Guard(tempfile::TempDir);

impl Guard {
	fn path(&self) -> &Path {
		self.0.path()
	}
}

/// Benchmarking/test context holding instantiated client and backend references.
pub struct BenchContext {
	/// Node client.
	pub client: Client,
	/// Node backend.
	pub backend: Arc<Backend>,

	db_guard: Guard,
}

type AccountPublic = <Signature as Verify>::Signer;

fn get_from_seed<TPublic: Public>(seed: &str) -> <TPublic::Pair as Pair>::Public {
	TPublic::Pair::from_string(&format!("//{}", seed), None)
		.expect("static values are valid; qed")
		.public()
}

fn get_account_id_from_seed<TPublic: Public>(seed: &str) -> AccountId
where
	AccountPublic: From<<TPublic::Pair as Pair>::Public>
{
	AccountPublic::from(get_from_seed::<TPublic>(seed)).into_account()
}

impl BenchContext {
	/// Import some block.
	pub fn import_block(&mut self, block: Block) {
		let mut import_params = BlockImportParams::new(BlockOrigin::NetworkBroadcast, block.header.clone());
		import_params.body = Some(block.extrinsics().to_vec());
		import_params.fork_choice = Some(ForkChoiceStrategy::LongestChain);

		assert_eq!(self.client.chain_info().best_number, 0);

		assert_eq!(
			self.client.import_block(import_params, Default::default())
				.expect("Failed to import block"),
			ImportResult::Imported(
				ImportedAux {
					header_only: false,
					clear_justification_requests: false,
					needs_justification: false,
					bad_justification: false,
					needs_finality_proof: false,
					is_new_best: true,
				}
			)
		);

		assert_eq!(self.client.chain_info().best_number, 1);
	}

	/// Database path for the current context.
	pub fn path(&self) -> &Path {
		self.db_guard.path()
	}
}
