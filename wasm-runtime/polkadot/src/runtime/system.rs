use primitives::{Block, BlockNumber, Hash, UncheckedTransaction, TxOrder, Hashable};
use runtime_support::{Vec, swap};
use storage::Storage;
use keyedvec::KeyedVec;
use environment::with_env;
use runtime::staking;

/// The current block number being processed. Set by `execute_block`.
pub fn block_number() -> BlockNumber {
	with_env(|e| e.block_number)
}

/// Get the block hash of a given block (uses storage).
pub fn block_hash(number: BlockNumber) -> Hash {
	Storage::into(&number.to_keyed_vec(b"sys\0old\0"))
}

/// Deposits a log and ensures it matches the blocks log data.
pub fn deposit_log(log: &[u8]) {
	with_env(|e| {
		assert_eq!(log, &e.digest.logs[e.next_log_index][..]);
		e.next_log_index += 1;
	});
}

pub fn execute_block(mut block: Block) {
	// populate environment from header.
	with_env(|e| {
		e.block_number = block.header.number;
		swap(&mut e.digest, &mut block.header.digest);
		e.next_log_index = 0;
	});

	let ref header = block.header;

	// check parent_hash is correct.
	assert!(
		header.number > 0 && block_hash(header.number - 1) == header.parent_hash,
		"Parent hash should be valid."
	);

	// TODO: check transaction trie root represents the transactions.

	// store the header hash in storage.
	let header_hash_key = header.number.to_keyed_vec(b"sys\0old\0");
	header.keccak256().store(&header_hash_key);

	// execute transactions
	staking::pre_transactions();
	block.transactions.iter().for_each(execute_transaction);
	staking::post_transactions();

	// any final checks
	final_checks(&block);

	// TODO: check storage root somehow
}

fn final_checks(_block: &Block) {
	with_env(|e| {
		assert_eq!(e.next_log_index, e.digest.logs.len());
	});
}

/// Execute a given transaction.
pub fn execute_transaction(utx: &UncheckedTransaction) {
	// Verify the signature is good.
	assert!(utx.ed25519_verify(), "All transactions should be properly signed");

	let ref tx = utx.transaction;

	// check nonce
	let nonce_key = tx.signed.to_keyed_vec(b"sys\0non\0");
	let expected_nonce: TxOrder = Storage::into(&nonce_key);
	assert!(tx.nonce == expected_nonce, "All transactions should have the correct nonce");

	// increment nonce in storage
	(expected_nonce + 1).store(&nonce_key);

	// decode parameters and dispatch
	tx.function.dispatch(&tx.signed, &tx.input_data);
}

/// Set the new code.
pub fn set_code(new: &[u8]) {
	new.store(b"\0code");
}

#[cfg(test)]
mod tests {
	use joiner::Joiner;
	use function::Function;
	use codec::keyedvec::KeyedVec;
	use std::collections::HashMap;
	use runtime_support::{NoError, with_externalities, Externalities};
	use primitives::{AccountID, UncheckedTransaction, Transaction};
	use runtime::{system, staking};

	#[derive(Debug, Default)]
	struct TestExternalities {
		storage: HashMap<Vec<u8>, Vec<u8>>,
	}
	impl Externalities for TestExternalities {
		type Error = NoError;

		fn storage(&self, key: &[u8]) -> Result<&[u8], NoError> {
			Ok(self.storage.get(&key.to_vec()).map_or(&[] as &[u8], Vec::as_slice))
		}

		fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>) {
			self.storage.insert(key, value);
		}

		fn chain_id(&self) -> u64 { 42 }
	}

	macro_rules! map {
		($( $name:expr => $value:expr ),*) => (
			vec![ $( ( $name, $value ) ),* ].into_iter().collect()
		)
	}

	#[test]
	fn staking_balance_transfer_dispatch_works() {
		let one: AccountID = [1u8; 32];
		let two: AccountID = [2u8; 32];

		let mut t = TestExternalities { storage: map![
			one.to_keyed_vec(b"sta\0bal\0") => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let tx = UncheckedTransaction {
			transaction: Transaction {
				signed: one.clone(),
				nonce: 0,
				function: Function::StakingTransferStake,
				input_data: vec![].join(&two).join(&69u64),
			},
			signature: [1u8; 64],
		};

		with_externalities(&mut t, || {
			system::execute_transaction(&tx);
			assert_eq!(staking::balance(&one), 42);
			assert_eq!(staking::balance(&two), 69);
		});
	}
}
