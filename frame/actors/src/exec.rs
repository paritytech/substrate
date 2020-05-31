use sp_core::H256;
use super::{Trait, MessageFor};

/// An interface that provides access to the external environment in which the
/// actor is executed.
pub trait Ext {
	type T: Trait;

	/// Returns the storage entry of the executing account by the given `key`.
	///
	/// Returns `None` if the `key` wasn't previously set by `set_storage` or
	/// was deleted.
	fn get_storage(&self, key: &H256) -> Option<Vec<u8>>;
	/// Sets the storage entry by the given key to the specified value. If `value` is `None` then
	/// the storage entry is deleted. Returns an Err if the value size is too large.
	fn set_storage(&self, key: H256, value: Option<Vec<u8>>) -> Result<(), &'static str>;
	/// Send a new message to other actors. Returns an Err if the fund cannot be paid by the current
	/// actor or if the message payload is too large.
	fn send_message(&self, message: MessageFor<Self::T>) -> Result<(), &'static str>;
	/// Get the message that the process function is currently operating on.
	fn get_message(&self) -> MessageFor<Self::T>;
}

/// A trait that represents a virtual machine.
pub trait Vm<T: Trait> {
	type Executable;

	/// Execute with an executable using the given `Ext` and message.
	fn execute<E: Ext<T = T>>(
		&self,
		exec: &Self::Executable,
		ext: E,
		message: MessageFor<T>,
	) -> Result<(), &'static str>;
}
