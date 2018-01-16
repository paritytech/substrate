use primitives::{Block, BlockNumber, Hash, Transaction};
use runtime_support::{Vec, swap};
use environment::with_env;
use staking;
use runtime_support;

/// The current block number being processed. Set by `execute_block`.
pub fn block_number() -> BlockNumber {
	with_env(|e| e.block_number)
}

/// Get the block hash of a given block (uses storage).
pub fn block_hash(_number: BlockNumber) -> Hash {
	unimplemented!()
}

/// Deposits a log and ensures it matches the blocks log data.
pub fn deposit_log(log: &[u8]) {
	with_env(|e| {
		assert_eq!(log, &e.digest.logs[e.next_log_index][..]);
		e.next_log_index += 1;
	});
}

pub fn execute_block(mut block: Block) -> Vec<u8> {
	// populate environment from header.
	with_env(|e| {
		e.block_number = block.header.number;
		swap(&mut e.digest, &mut block.header.digest);
		e.next_log_index = 0;
	});

	// TODO: check transaction trie root represents the transactions.
	// TODO: store the header hash in storage.

	staking::pre_transactions();

	block.transactions.iter().for_each(|tx| { execute_transaction(tx); });

	staking::post_transactions();

	final_checks(&block);

	// TODO: check state root somehow

	Vec::new()
}

fn final_checks(_block: &Block) {
	with_env(|e| {
		assert_eq!(e.next_log_index, e.digest.logs.len());
	});
}

/// Execute a given transaction.
pub fn execute_transaction(_tx: &Transaction) -> Vec<u8> {
	// TODO: decode data and ensure valid
	// TODO: ensure signature valid and recover id (use authentication::authenticate)
	// TODO: check nonce
	// TODO: increment nonce in storage
	// TODO: ensure target_function valid
	// TODO: decode parameters

	_tx.function.dispatch(&_tx.signed, &_tx.input_data);

	// TODO: encode any return
	Vec::new()
}

/// Set the new code.
pub fn set_code(new: &[u8]) {
	runtime_support::set_storage(b"\0code", new)
}

#[cfg(test)]
mod tests {
	use joiner::Joiner;
	use function::Function;
	use std::collections::HashMap;
	use runtime_support::{NoError, with_externalities, Externalities};
	use primitives::{AccountID, Transaction};
	use system;
	use staking;

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
			{ let mut r = b"sta\0bal\0".to_vec(); r.extend_from_slice(&one); r } => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
		], };

		let tx = Transaction {
			signed: one.clone(),
			function: Function::StakingTransferStake,
			input_data: vec![].join(&two).join(&69u64),
			nonce: 0,
		};

		with_externalities(&mut t, || {
			system::execute_transaction(&tx);
			assert_eq!(staking::balance(&one), 42);
			assert_eq!(staking::balance(&two), 69);
		});
	}
}
