// Copyright 2019-2021 Parity Technologies (UK) Ltd.
// This file is part of Cumulus.

// Cumulus is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Cumulus is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Cumulus.  If not, see <http://www.gnu.org/licenses/>.

//! A Cumulus test client.

mod block_builder;
use codec::Encode;
use runtime::{
	Balance, Block, BlockHashCount, Call, Runtime, Signature, SignedExtra, SignedPayload,
	UncheckedExtrinsic, VERSION,
};
use sc_service::client;
use sp_blockchain::HeaderBackend;
use sp_core::storage::Storage;
use sp_runtime::{generic::Era, BuildStorage, SaturatedConversion};

pub use block_builder::*;
pub use sc_executor::error::Result as ExecutorResult;
pub use substrate_test_client::*;
pub use test_runtime_grandpa as runtime;

mod local_executor {
	/// Native executor instance.
	pub struct LocalExecutor;

	impl sc_executor::NativeExecutionDispatch for LocalExecutor {
		type ExtendHostFunctions = ();

		fn dispatch(method: &str, data: &[u8]) -> Option<Vec<u8>> {
			test_runtime_grandpa::api::dispatch(method, data)
		}

		fn native_version() -> sc_executor::NativeVersion {
			test_runtime_grandpa::native_version()
		}
	}
}

/// Native executor used for tests.
pub use local_executor::LocalExecutor;

/// Test client database backend.
pub type Backend = substrate_test_client::Backend<Block>;

/// Test client executor.
pub type Executor =
	client::LocalCallExecutor<Block, Backend, sc_executor::NativeElseWasmExecutor<LocalExecutor>>;

/// Test client builder for Cumulus
pub type TestClientBuilder =
	substrate_test_client::TestClientBuilder<Block, Executor, Backend, GenesisParameters>;

/// LongestChain type for the test runtime/client.
pub type LongestChain = sc_consensus::LongestChain<Backend, Block>;

/// Test client type with `LocalExecutor` and generic Backend.
pub type Client = client::Client<Backend, Executor, Block, runtime::RuntimeApi>;

/// Parameters of test-client builder with test-runtime.
#[derive(Default)]
pub struct GenesisParameters;

impl substrate_test_client::GenesisInit for GenesisParameters {
	fn genesis_storage(&self) -> Storage {
		test_service_grandpa::local_testnet_genesis().build_storage().unwrap()
	}
}

/// A `test-runtime` extensions to `TestClientBuilder`.
pub trait TestClientBuilderExt: Sized {
	/// Build the test client.
	fn build(self) -> Client {
		self.build_with_longest_chain().0
	}

	/// Build the test client and longest chain selector.
	fn build_with_longest_chain(self) -> (Client, LongestChain);
}

impl TestClientBuilderExt for TestClientBuilder {
	fn build_with_longest_chain(self) -> (Client, LongestChain) {
		self.build_with_native_executor(None)
	}
}

/// A `TestClientBuilder` with default backend and executor.
pub trait DefaultTestClientBuilderExt: Sized {
	/// Create new `TestClientBuilder`
	fn new() -> Self;
}

impl DefaultTestClientBuilderExt for TestClientBuilder {
	fn new() -> Self {
		Self::with_default_backend()
	}
}

/// Generate an extrinsic from the provided function call, origin and [`Client`].
pub fn generate_extrinsic(
	client: &Client,
	origin: sp_keyring::AccountKeyring,
	function: Call,
) -> UncheckedExtrinsic {
	let current_block_hash = client.info().best_hash;
	let current_block = client.info().best_number.saturated_into();
	let genesis_block = client.hash(0).unwrap().unwrap();
	let nonce = 0;
	let period =
		BlockHashCount::get().checked_next_power_of_two().map(|c| c / 2).unwrap_or(2) as u64;

	let extra: SignedExtra = (
		frame_system::CheckSpecVersion::<Runtime>::new(),
		frame_system::CheckGenesis::<Runtime>::new(),
		frame_system::CheckEra::<Runtime>::from(Era::mortal(period, current_block)),
		frame_system::CheckNonce::<Runtime>::from(nonce),
		frame_system::CheckWeight::<Runtime>::new(),
	);
	let raw_payload = SignedPayload::from_raw(
		function.clone(),
		extra.clone(),
		(VERSION.spec_version, genesis_block, current_block_hash, (), ()),
	);
	let signature = raw_payload.using_encoded(|e| origin.sign(e));

	UncheckedExtrinsic::new_signed(
		function.clone(),
		origin.public().into(),
		Signature::Sr25519(signature.clone()),
		extra.clone(),
	)
}

/// Transfer some token from one account to another using a provided test [`Client`].
pub fn transfer(
	client: &Client,
	origin: sp_keyring::AccountKeyring,
	dest: sp_keyring::AccountKeyring,
	value: Balance,
) -> UncheckedExtrinsic {
	let function =
		Call::Balances(pallet_balances::Call::transfer { dest: dest.public().into(), value });

	generate_extrinsic(client, origin, function)
}

// /// Call `validate_block` in the given `wasm_blob`.
// pub fn validate_block(
// 	validation_params: ValidationParams,
// 	wasm_blob: &[u8],
// ) -> ExecutorResult<ValidationResult> {
// 	let mut ext = TestExternalities::default();
// 	let mut ext_ext = ext.ext();

// 	let executor = WasmExecutor::new(
// 		WasmExecutionMethod::Interpreted,
// 		Some(1024),
// 		sp_io::SubstrateHostFunctions::host_functions(),
// 		1,
// 		None,
// 	);

// 	executor
// 		.uncached_call(
// 			RuntimeBlob::uncompress_if_needed(wasm_blob).expect("RuntimeBlob uncompress & parse"),
// 			&mut ext_ext,
// 			false,
// 			"validate_block",
// 			&validation_params.encode(),
// 		)
// 		.map(|v| ValidationResult::decode(&mut &v[..]).expect("Decode `ValidationResult`."))
// 		.map_err(|err| err.into())
// }
