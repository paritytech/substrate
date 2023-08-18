pub use crate::exec::ExportedFunction;
use crate::{CodeHash, Config, LOG_TARGET};
use pallet_contracts_primitives::ExecReturnValue;

/// Defines the interface between pallet contracts and the outside observer.
///
/// The intended use is the environment, where the observer holds directly the whole runtime
/// (externalities) and thus can react to the execution breakpoints synchronously.
pub trait CallSpan<T: Config> where Self: Sized {
	/// Called just before the execution of a contract.
	///
	/// # Arguments
	///
	/// * `code_hash` - The code hash of the contract being called.
	/// * `entry_point` - Describes whether the call is the constructor or a regular call.
	/// * `input_data` - The raw input data of the call.
	fn before_call(
		code_hash: &CodeHash<T>,
		entry_point: ExportedFunction,
		input_data: &[u8],
	) -> Self;

	/// Called just after the execution of a contract.
	///
	/// # Arguments
	///
	/// * `output` - The raw output of the call.
	fn after_call(self, output: &ExecReturnValue) {
		log::trace!(target: LOG_TARGET, "call result {output:?}")
	}
}


impl<T: Config> CallSpan<T> for () {
	fn before_call(
		code_hash: &CodeHash<T>,
		entry_point: ExportedFunction,
		input_data: &[u8],
	) {
		log::trace!(target: LOG_TARGET, "call {entry_point:?} hash: {code_hash:?}, input_data: {input_data:?}")
	}

	fn after_call(self, output: &ExecReturnValue) {
		log::trace!(target: LOG_TARGET, "call result {output:?}")
	}
}
