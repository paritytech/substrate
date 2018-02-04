use std::panic::catch_unwind;
use primitives::contract::CallData;
use state_machine::{Externalities, CodeExecutor};
use error::{Error, ErrorKind, Result};
use wasm_executor::WasmExecutor;
use native_runtime as runtime;
use runtime_std;

pub struct NativeExecutor;

fn safe_call<F: ::std::panic::UnwindSafe + FnOnce() -> Vec<u8>>(f: F) -> Result<Vec<u8>> {
	catch_unwind(f).map_err(|_| ErrorKind::Runtime.into())
}

impl CodeExecutor for NativeExecutor {
	type Error = Error;

	fn call<E: Externalities>(
		&self,
		ext: &mut E,
		code: &[u8],
		method: &str,
		data: &CallData,
	) -> Result<Vec<u8>> {
		// WARNING!!! This assumes that the runtime was built *before* the main project. Until we
		// get a proper build script, this must be strictly adhered to or things will go wrong.
		let native_equivalent = include_bytes!("../../wasm-runtime/target/wasm32-unknown-unknown/release/runtime_polkadot.compact.wasm");
		if code == &native_equivalent[..] {
			runtime_std::with_externalities(ext, || match method {
				"execute_block" => safe_call(|| runtime::execute_block(&data.0)),
				"execute_transaction" => safe_call(|| runtime::execute_transaction(&data.0)),
				_ => Err(ErrorKind::MethodNotFound(method.to_owned()).into()),
			})
		} else {
			// call into wasm.
			WasmExecutor.call(ext, code, method, data)
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_std::TestExternalities;
	use native_runtime::codec::{KeyedVec, Joiner, Slicable};
	use native_runtime::support::{one, two, StaticHexInto, Hashable};
	use native_runtime::primitives::*;
	use native_runtime::runtime::staking::balance;
	use primitives::twox_128;

	const BLOATY_CODE: &[u8] = include_bytes!("../../wasm-runtime/target/wasm32-unknown-unknown/release/runtime_polkadot.wasm");
	const COMPACT_CODE: &[u8] = include_bytes!("../../wasm-runtime/target/wasm32-unknown-unknown/release/runtime_polkadot.compact.wasm");
	fn tx() -> UncheckedTransaction {
		let transaction = Transaction {
			signed: one(),
			nonce: 0,
			function: Function::StakingTransfer,
			input_data: two().to_vec().join(&69u64),
		};
		let signature = secret_for(&transaction.signed).unwrap()
			.sign(&transaction.to_vec())
			.inner();
		UncheckedTransaction { transaction, signature }
	}

	#[test]
	fn panic_execution_with_foreign_code_gives_error() {
		let one = one();
		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![68u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let r = NativeExecutor.call(&mut t, BLOATY_CODE, "execute_transaction", &CallData(vec![].join(&1u64).join(&tx())));
		assert!(r.is_err());
	}

	#[test]
	fn panic_execution_with_native_equivalent_code_gives_error() {
		let one = one();
		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![68u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let r = NativeExecutor.call(&mut t, COMPACT_CODE, "execute_transaction", &CallData(vec![].join(&1u64).join(&tx())));
		assert!(r.is_err());
	}

	#[test]
	fn successful_execution_with_native_equivalent_code_gives_ok() {
		let one = one();
		let two = two();

		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let r = NativeExecutor.call(&mut t, COMPACT_CODE, "execute_transaction", &CallData(vec![].join(&1u64).join(&tx())));
		assert!(r.is_ok());

		runtime_std::with_externalities(&mut t, || {
			assert_eq!(balance(&one), 42);
			assert_eq!(balance(&two), 69);
		});
	}

	#[test]
	fn successful_execution_with_foreign_code_gives_ok() {
		let one = one();
		let two = two();

		let mut t = TestExternalities { storage: map![
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let r = NativeExecutor.call(&mut t, BLOATY_CODE, "execute_transaction", &CallData(vec![].join(&1u64).join(&tx())));
		assert!(r.is_ok());

		runtime_std::with_externalities(&mut t, || {
			assert_eq!(balance(&one), 42);
			assert_eq!(balance(&two), 69);
		});
	}

	fn new_test_ext() -> TestExternalities {
		let one = one();
		let two = two();
		let three = [3u8; 32];

		TestExternalities { storage: map![
			twox_128(&0u64.to_keyed_vec(b"sys:old:")).to_vec() => [69u8; 32].to_vec(),
			twox_128(b"gov:apr").to_vec() => vec![].join(&667u32),
			twox_128(b"ses:len").to_vec() => vec![].join(&2u64),
			twox_128(b"ses:val:len").to_vec() => vec![].join(&3u32),
			twox_128(&0u32.to_keyed_vec(b"ses:val:")).to_vec() => one.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"ses:val:")).to_vec() => two.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"ses:val:")).to_vec() => three.to_vec(),
			twox_128(b"sta:wil:len").to_vec() => vec![].join(&3u32),
			twox_128(&0u32.to_keyed_vec(b"sta:wil:")).to_vec() => one.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"sta:wil:")).to_vec() => two.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"sta:wil:")).to_vec() => three.to_vec(),
			twox_128(b"sta:spe").to_vec() => vec![].join(&2u64),
			twox_128(b"sta:vac").to_vec() => vec![].join(&3u64),
			twox_128(b"sta:era").to_vec() => vec![].join(&0u64),
			twox_128(&one.to_keyed_vec(b"sta:bal:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], }
	}

	use primitives::ed25519::Pair;
	fn secret_for(who: &AccountID) -> Option<Pair> {
		match who {
			x if *x == one() => Some(Pair::from_seed(b"12345678901234567890123456789012")),
			x if *x == two() => Some("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60".into()),
			_ => None,
		}
	}

	fn construct_block(number: BlockNumber, parent_hash: Hash, state_root: Hash, txs: Vec<Transaction>) -> (Vec<u8>, Hash) {
		use triehash::ordered_trie_root;

		let transactions = txs.into_iter().map(|transaction| {
			let signature = secret_for(&transaction.signed).unwrap()
				.sign(&transaction.to_vec())
				.inner();
			UncheckedTransaction { transaction, signature }
		}).collect::<Vec<_>>();

		let transaction_root = ordered_trie_root(transactions.iter().map(Slicable::to_vec)).0;

		let header = Header {
			parent_hash,
			number,
			state_root,
			transaction_root,
			digest: Digest { logs: vec![], },
		};
		let hash = header.blake2_256();

		(Block { header, transactions }.to_vec(), hash)
	}

	fn block1() -> (Vec<u8>, Hash) {
		construct_block(
			1,
			[69u8; 32],
			hex!("2481853da20b9f4322f34650fea5f240dcbfb266d02db94bfa0153c31f4a29db"),
			vec![Transaction {
				signed: one(),
				nonce: 0,
				function: Function::StakingTransfer,
				input_data: vec![].join(&two()).join(&69u64),
			}]
		)
	}

	fn block2() -> (Vec<u8>, Hash) {
		construct_block(
			2,
			block1().1,
			hex!("2e69e4405a13981224078ad5355c68401bf56d0fe3f14a3536734666e6a8a047"),
			vec![
				Transaction {
					signed: two(),
					nonce: 0,
					function: Function::StakingTransfer,
					input_data: vec![].join(&one()).join(&5u64),
				},
				Transaction {
					signed: one(),
					nonce: 1,
					function: Function::StakingTransfer,
					input_data: vec![].join(&two()).join(&15u64),
				}
			]
		)
	}

	#[test]
	fn test_execution_works() {
		let mut t = new_test_ext();
		println!("Testing Wasm...");
		let r = WasmExecutor.call(&mut t, COMPACT_CODE, "run_tests", &CallData(block2().0));
		assert!(r.is_ok());
	}

	#[test]
	fn full_native_block_import_works() {
		let mut t = new_test_ext();

		NativeExecutor.call(&mut t, COMPACT_CODE, "execute_block", &CallData(block1().0)).unwrap();

		runtime_std::with_externalities(&mut t, || {
			assert_eq!(balance(&one()), 42);
			assert_eq!(balance(&two()), 69);
		});

		NativeExecutor.call(&mut t, COMPACT_CODE, "execute_block", &CallData(block2().0)).unwrap();

		runtime_std::with_externalities(&mut t, || {
			assert_eq!(balance(&one()), 32);
			assert_eq!(balance(&two()), 79);
		});
	}

	#[test]
	fn full_wasm_block_import_works() {
		let mut t = new_test_ext();

		WasmExecutor.call(&mut t, COMPACT_CODE, "execute_block", &CallData(block1().0)).unwrap();

		runtime_std::with_externalities(&mut t, || {
			assert_eq!(balance(&one()), 42);
			assert_eq!(balance(&two()), 69);
		});

		WasmExecutor.call(&mut t, COMPACT_CODE, "execute_block", &CallData(block2().0)).unwrap();

		runtime_std::with_externalities(&mut t, || {
			assert_eq!(balance(&one()), 32);
			assert_eq!(balance(&two()), 79);
		});
	}
}
