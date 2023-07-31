use crate::exec::ExportedFunction;
use pallet_contracts_primitives::ExecReturnValue;

/// Defines the interface between pallet contracts and the outside observer.
///
/// The intended use is the environment, where the observer holds directly the whole runtime
/// (externalities) and thus can react to the execution breakpoints synchronously.
///
/// This definitely *should not* be used in any production or benchmarking setting, since handling
/// callbacks might be arbitrarily expensive and thus significantly influence performance.
pub trait ExecutionObserver<CodeHash> {
	/// Called just before the execution of a contract.
	///
	/// # Arguments
	///
	/// * `code_hash` - The code hash of the contract being called.
	/// * `entry_point` - Describes whether the call is the constructor or a regular call.
	/// * `input_data` - The raw input data of the call.
	fn before_call(_code_hash: &CodeHash, _entry_point: ExportedFunction, _input_data: &[u8]) {}

	/// Called just after the execution of a contract.
	///
	/// # Arguments
	///
	/// * `code_hash` - The code hash of the contract being called.
	/// * `entry_point` - Describes whether the call was the constructor or a regular call.
	/// * `input_data` - The raw input data of the call.
	/// * `output` - The raw output of the call.
	fn after_call(
		_code_hash: &CodeHash,
		_entry_point: ExportedFunction,
		_input_data: &[u8],
		_output: &ExecReturnValue,
	) {
	}
}
