use codec::{Encode, Decode};
use sp_runtime::traits::Bounded;
use crate::{
	Trait, AccountIdFor, BalanceFor, MessageFor, StorageKey, Gas, Schedule,
	Token, gas::{GasMeter, GasMeterResult},
};

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
	fn set_storage(&mut self, key: StorageKey, value: Option<Vec<u8>>) -> Result<(), &'static str>;
	/// Send a new message to other actors. Returns an Err if the fund cannot be paid by the current
	/// actor or if the message payload is too large.
	fn send_message(
		&mut self,
		target: AccountIdFor<Self::T>,
		value: BalanceFor<Self::T>,
		data: Vec<u8>,
	) -> Result<(), &'static str>;
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
	/// Signals that trap was generated because the contract exhausted its gas limit.
	OutOfGas,
	/// Signals that a trap was generated in response to a succesful call to the
	/// `ext_terminate` host function.
	Termination,
}

#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[derive(Copy, Clone)]
pub enum RuntimeToken {
	/// Explicit call to the `gas` function. Charge the gas meter
	/// with the value provided.
	Explicit(u32),
	/// The given number of bytes is read from the sandbox memory.
	ReadMemory(u32),
	/// The given number of bytes is written to the sandbox memory.
	WriteMemory(u32),
	/// (topic_count, data_bytes): A buffer of the given size is posted as an event indexed with the
	/// given number of topics.
	DepositEvent(u32, u32),
}

impl<T: Trait> Token<T> for RuntimeToken {
	type Metadata = Schedule;

	fn calculate_amount(&self, metadata: &Schedule) -> Gas {
		use self::RuntimeToken::*;
		let value = match *self {
			Explicit(amount) => Some(amount.into()),
			ReadMemory(byte_count) => metadata
				.sandbox_data_read_cost
				.checked_mul(byte_count.into()),
			WriteMemory(byte_count) => metadata
				.sandbox_data_write_cost
				.checked_mul(byte_count.into()),
			DepositEvent(topic_count, data_byte_count) => {
				let data_cost = metadata
					.event_data_per_byte_cost
					.checked_mul(data_byte_count.into());

				let topics_cost = metadata
					.event_per_topic_cost
					.checked_mul(topic_count.into());

				data_cost
					.and_then(|data_cost| {
						topics_cost.and_then(|topics_cost| {
							data_cost.checked_add(topics_cost)
						})
					})
					.and_then(|data_and_topics_cost|
						data_and_topics_cost.checked_add(metadata.event_base_cost)
					)
			},
		};

		value.unwrap_or_else(|| Bounded::max_value())
	}
}

pub struct Runtime<'a, E: Ext + 'a> {
	ext: &'a mut E,
	scratch_buf: Vec<u8>,
	schedule: &'a Schedule,
	memory: sp_sandbox::Memory,
	gas_meter: &'a mut GasMeter<E::T>,
	special_trap: Option<SpecialTrap>,
}

impl<'a, E: Ext + 'a> Runtime<'a, E> {
	pub(crate) fn new(
		ext: &'a mut E,
		input_data: Vec<u8>,
		schedule: &'a Schedule,
		memory: sp_sandbox::Memory,
		gas_meter: &'a mut GasMeter<E::T>,
	) -> Self {
		Runtime {
			ext,
			// Put the input data into the scratch buffer immediately.
			scratch_buf: input_data,
			memory,
			special_trap: None,
			schedule,
			gas_meter,
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

	/// Charge the gas meter with the specified token.
	///
	/// Returns `Err(HostError)` if there is not enough gas.
	fn charge_gas(
		&mut self,
		token: RuntimeToken,
	) -> Result<(), sp_sandbox::HostError> {
		match self.gas_meter.charge(self.schedule, token) {
			GasMeterResult::Proceed => Ok(()),
			GasMeterResult::OutOfGas =>  {
				self.special_trap = Some(SpecialTrap::OutOfGas);
				Err(sp_sandbox::HostError)
			},
		}
	}
}

// Define a function `fn init_env<E: Ext>() -> HostFunctionSet<E>` that returns
// a function set which can be imported by an executed contract.
define_env!(
	Env, <E: Ext>,

	// Account for used gas. Traps if gas used is greater than gas limit.
	//
	// NOTE: This is a implementation defined call and is NOT a part of the public API.
	// This call is supposed to be called only by instrumentation injected code.
	//
	// - amount: How much gas is used.
	gas(ctx: &mut Runtime<E>, amount: u32) => {
		ctx.charge_gas(RuntimeToken::Explicit(amount))?;
		Ok(())
	},

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

	// Retrieve the value under the given key from the storage and return 0.
	// If there is no entry under the given key then this function will return 1 and
	// clear the scratch buffer.
	//
	// - key_ptr: pointer into the linear memory where the key
	//   of the requested value is placed.
	ext_get_storage(ctx: &mut Runtime<E>, key_ptr: u32) -> u32 => {
		let mut key: StorageKey = [0; 32];
		ctx.read_sandbox_memory_into_buf(key_ptr, &mut key)?;
		if let Some(value) = ctx.ext.get_storage(&key) {
			ctx.scratch_buf = value;
			Ok(0)
		} else {
			ctx.scratch_buf.clear();
			Ok(1)
		}
	},

	// Retrieve the message.
	ext_get_message(ctx: &mut Runtime<E>) -> u32 => {
		ctx.scratch_buf = ctx.ext.get_message().encode();
		Ok(0)
	},

	// Send a message.
	ext_send_message(
		ctx: &mut Runtime<E>,
		target_ptr: u32, target_len: u32,
		value_ptr: u32, value_len: u32,
		data_ptr: u32, data_len: u32
	) -> u32 => {
		let target: AccountIdFor<E::T> = ctx.read_sandbox_memory_as(target_ptr, target_len)?;
		let value: BalanceFor<E::T> = ctx.read_sandbox_memory_as(value_ptr, value_len)?;
		let data: Vec<u8> = ctx.read_sandbox_memory_as(data_ptr, data_len)?;

		match ctx.ext.send_message(target, value, data) {
			Ok(_) => Ok(0),
			Err(_) => Ok(1),
		}
	},

	// Prints utf8 encoded string from the data buffer.
	// Only available on `--dev` chains.
	// This function may be removed at any time, superseded by a more general contract debugging feature.
	ext_println(ctx, str_ptr: u32, str_len: u32) => {
		let data = read_sandbox_memory(ctx, str_ptr, str_len)?;
		if let Ok(utf8) = core::str::from_utf8(&data) {
			sp_runtime::print(utf8);
		}
		Ok(())
	},
);
