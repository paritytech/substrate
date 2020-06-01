#[macro_use]
mod env_def;

use codec::Decode;
use sp_core::H256;
use crate::{Trait, MessageFor, exec::StorageKey};

/// An interface that provides access to the external environment in which the
/// actor is executed.
pub trait Ext {
	type T: Trait;

	/// Returns the storage entry of the executing account by the given `key`.
	///
	/// Returns `None` if the `key` wasn't previously set by `set_storage` or
	/// was deleted.
	fn get_storage(&self, key: &StorageKey) -> Option<Vec<u8>>;
	/// Sets the storage entry by the given key to the specified value. If `value` is `None` then
	/// the storage entry is deleted. Returns an Err if the value size is too large.
	fn set_storage(&self, key: StorageKey, value: Option<Vec<u8>>) -> Result<(), &'static str>;
	/// Send a new message to other actors. Returns an Err if the fund cannot be paid by the current
	/// actor or if the message payload is too large.
	fn send_message(&self, message: MessageFor<Self::T>) -> Result<(), &'static str>;
	/// Get the message that the process function is currently operating on.
	fn get_message(&self) -> MessageFor<Self::T>;
	/// Returns the maximum allowed size of a storage item.
	fn max_value_size(&self) -> u32;
}

/// Enumerates all possible *special* trap conditions.
///
/// In this runtime traps used not only for signaling about errors but also
/// to just terminate quickly in some cases.
enum SpecialTrap {
	/// Signals that trap was generated in response to call `ext_return` host function.
	Return(Vec<u8>),
	/// Signals that trap was generated because the contract exhausted its gas limit.
	OutOfGas,
	/// Signals that a trap was generated in response to a succesful call to the
	/// `ext_terminate` host function.
	Termination,
}

pub struct Runtime<'a, E: Ext + 'a> {
	ext: &'a mut E,
	scratch_buf: Vec<u8>,
	memory: sp_sandbox::Memory,
	special_trap: Option<SpecialTrap>,
}

impl<'a, E: Ext + 'a> Runtime<'a, E> {
	pub(crate) fn new(
		ext: &'a mut E,
		input_data: Vec<u8>,
		memory: sp_sandbox::Memory,
	) -> Self {
		Runtime {
			ext,
			// Put the input data into the scratch buffer immediately.
			scratch_buf: input_data,
			memory,
			special_trap: None,
		}
	}

	/// Read designated chunk from the sandbox memory, consuming an appropriate amount of
	/// gas.
	///
	/// Returns `Err` if one of the following conditions occurs:
	///
	/// - calculating the gas cost resulted in overflow.
	/// - out of gas
	/// - requested buffer is not within the bounds of the sandbox memory.
	fn read_sandbox_memory(
		&mut self,
		ptr: u32,
		len: u32,
	) -> Result<Vec<u8>, sp_sandbox::HostError> {
		let mut buf = vec![0u8; len as usize];
		self.memory.get(ptr, buf.as_mut_slice()).map_err(|_| sp_sandbox::HostError)?;
		Ok(buf)
	}

	/// Read designated chunk from the sandbox memory into the scratch buffer, consuming an
	/// appropriate amount of gas. Resizes the scratch buffer to the specified length on success.
	///
	/// Returns `Err` if one of the following conditions occurs:
	///
	/// - calculating the gas cost resulted in overflow.
	/// - out of gas
	/// - requested buffer is not within the bounds of the sandbox memory.
	fn read_sandbox_memory_into_scratch(
		&mut self,
		ptr: u32,
		len: u32,
	) -> Result<(), sp_sandbox::HostError> {
		self.scratch_buf.resize(len as usize, 0);
		self.memory.get(ptr, self.scratch_buf.as_mut_slice()).map_err(|_| sp_sandbox::HostError)?;
		Ok(())
	}

	/// Read designated chunk from the sandbox memory into the supplied buffer, consuming
	/// an appropriate amount of gas.
	///
	/// Returns `Err` if one of the following conditions occurs:
	///
	/// - calculating the gas cost resulted in overflow.
	/// - out of gas
	/// - requested buffer is not within the bounds of the sandbox memory.
	fn read_sandbox_memory_into_buf(
		&mut self,
		ptr: u32,
		buf: &mut [u8],
	) -> Result<(), sp_sandbox::HostError> {
		self.memory.get(ptr, buf).map_err(Into::into)
	}

	/// Read designated chunk from the sandbox memory, consuming an appropriate amount of
	/// gas, and attempt to decode into the specified type.
	///
	/// Returns `Err` if one of the following conditions occurs:
	///
	/// - calculating the gas cost resulted in overflow.
	/// - out of gas
	/// - requested buffer is not within the bounds of the sandbox memory.
	/// - the buffer contents cannot be decoded as the required type.
	fn read_sandbox_memory_as<D: Decode>(
		&mut self,
		ptr: u32,
		len: u32,
	) -> Result<D, sp_sandbox::HostError> {
		let buf = self.read_sandbox_memory(ptr, len)?;
		D::decode(&mut &buf[..]).map_err(|_| sp_sandbox::HostError)
	}

	/// Write the given buffer to the designated location in the sandbox memory, consuming
	/// an appropriate amount of gas.
	///
	/// Returns `Err` if one of the following conditions occurs:
	///
	/// - calculating the gas cost resulted in overflow.
	/// - out of gas
	/// - designated area is not within the bounds of the sandbox memory.
	fn write_sandbox_memory(
		&mut self,
		ptr: u32,
		buf: &[u8],
	) -> Result<(), sp_sandbox::HostError> {
		self.memory.set(ptr, buf)?;

		Ok(())
	}

}

// Define a function `fn init_env<E: Ext>() -> HostFunctionSet<E>` that returns
// a function set which can be imported by an executed contract.
define_env!(
	Env, <E: Ext>,

	// Set the value at the given key in the contract storage.
	//
	// The value length must not exceed the maximum defined by the contracts module parameters.
	// Storing an empty value is disallowed.
	//
	// # Parameters
	//
	// - `key_ptr`: pointer into the linear memory where the location to store the value is placed.
	// - `value_ptr`: pointer into the linear memory where the value to set is placed.
	// - `value_len`: the length of the value in bytes.
	//
	// # Errors
	//
	// - If value length exceeds the configured maximum value length of a storage entry.
	// - Upon trying to set an empty storage entry (value length is 0).
	ext_set_storage(ctx: &mut Runtime<E>, key_ptr: u32, value_ptr: u32, value_len: u32) => {
		if value_len > ctx.ext.max_value_size() {
			// Bail out if value length exceeds the set maximum value size.
			return Err(sp_sandbox::HostError);
		}
		let mut key: StorageKey = [0; 32];
		ctx.read_sandbox_memory_into_buf(key_ptr, &mut key)?;
		let value = Some(ctx.read_sandbox_memory(value_ptr, value_len)?);
		ctx.ext.set_storage(key, value).map_err(|_| sp_sandbox::HostError)?;
		Ok(())
	},
);
