pub enum TxOutcome {
	Commit,
	Discard,
}

pub fn with_transaction<R>(f: impl FnOnce() -> (R, TxOutcome)) -> R {
	use sp_io::storage::{
		start_transaction, commit_transaction, discard_transaction,
	};

	start_transaction();
	let (result, outcome) = f();
	match outcome {
		TxOutcome::Commit => commit_transaction(),
		TxOutcome::Discard => discard_transaction(),
	}
	result
}
