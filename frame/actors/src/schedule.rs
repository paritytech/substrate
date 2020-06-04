#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use codec::{Encode, Decode};
use sp_runtime::RuntimeDebug;
use crate::gas::Gas;

/// Definition of the cost schedule and other parameterizations for wasm vm.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Clone, Encode, Decode, PartialEq, Eq, RuntimeDebug)]
pub struct Schedule {
	/// Version of the schedule.
	pub version: u32,

	/// Cost of putting a byte of code into storage.
	pub put_code_per_byte_cost: Gas,

	/// Gas cost of a growing memory by single page.
	pub grow_mem_cost: Gas,

	/// Gas cost of a regular operation.
	pub regular_op_cost: Gas,

	/// Gas cost to deposit an event; the per-byte portion.
	pub message_data_per_byte_cost: Gas,

	/// Gas cost to deposit an event; the cost per topic.
	pub message_per_topic_cost: Gas,

	/// Gas cost to deposit an event; the base.
	pub message_base_cost: Gas,

	/// Gas cost per one byte read from the sandbox memory.
	pub sandbox_data_read_cost: Gas,

	/// Gas cost per one byte written to the sandbox memory.
	pub sandbox_data_write_cost: Gas,

	/// The maximum number of topics supported by an event.
	pub max_event_topics: u32,

	/// Maximum allowed stack height.
	///
	/// See https://wiki.parity.io/WebAssembly-StackHeight to find out
	/// how the stack frame cost is calculated.
	pub max_stack_height: u32,

	/// Maximum number of memory pages allowed for a contract.
	pub max_memory_pages: u32,

	/// Maximum allowed size of a declared table.
	pub max_table_size: u32,

	/// Maximum value size.
	pub max_value_size: u32,

	/// Whether println is enabled.
	pub enable_println: bool,
}

// 500 (2 instructions per nano second on 2GHZ) * 1000x slowdown through wasmi
// This is a wild guess and should be viewed as a rough estimation.
// Proper benchmarks are needed before this value and its derivatives can be used in production.
const WASM_INSTRUCTION_COST: Gas = 500_000;

impl Default for Schedule {
	fn default() -> Schedule {
		Schedule {
			version: 0,
			put_code_per_byte_cost: WASM_INSTRUCTION_COST,
			grow_mem_cost: WASM_INSTRUCTION_COST,
			regular_op_cost: WASM_INSTRUCTION_COST,
			message_data_per_byte_cost: WASM_INSTRUCTION_COST,
			message_per_topic_cost: WASM_INSTRUCTION_COST,
			message_base_cost: WASM_INSTRUCTION_COST,
			sandbox_data_read_cost: WASM_INSTRUCTION_COST,
			sandbox_data_write_cost: WASM_INSTRUCTION_COST,
			max_event_topics: 4,
			max_stack_height: 64 * 1024,
			max_memory_pages: 16,
			max_table_size: 16 * 1024,
			max_value_size: 1024,
			enable_println: false,
		}
	}
}
