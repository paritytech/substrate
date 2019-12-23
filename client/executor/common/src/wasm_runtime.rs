use crate::error::Error;
use sp_core::traits::Externalities;
use sp_wasm_interface::Function;

/// The Substrate Wasm runtime.
pub trait WasmRuntime {
	/// Attempt to update the number of heap pages available during execution.
	///
	/// Returns false if the update cannot be applied. The function is guaranteed to return true if
	/// the heap pages would not change from its current value.
	fn update_heap_pages(&mut self, heap_pages: u64) -> bool;

	/// Return the host functions that are registered for this Wasm runtime.
	fn host_functions(&self) -> &[&'static dyn Function];

	/// Call a method in the Substrate runtime by name. Returns the encoded result on success.
	fn call(&mut self, ext: &mut dyn Externalities, method: &str, data: &[u8])
		-> Result<Vec<u8>, Error>;
}
