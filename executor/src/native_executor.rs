use primitives::contract::CallData;
use state_machine::{Externalities, CodeExecutor};
//use error::{Error, ErrorKind, Result};
use native_runtime as runtime;
use runtime_support;

struct NativeExecutor;

impl CodeExecutor for NativeExecutor {
	type Error = runtime_support::NoError;

	fn call<E: Externalities>(
		&self,
		ext: &mut E,
		code: &[u8],
		method: &str,
		data: &CallData,
	) -> ::std::result::Result<Vec<u8>, Self::Error> {
		// WARNING!!! This assumes that the runtime was build *before* the main project. Until we
		// get a proper build script, this must be strictly adhered to or things will go wrong.
		let native_equivalent = include_bytes!("../../wasm-runtime/target/wasm32-unknown-unknown/release/runtime_polkadot.compact.wasm");
		if code == &native_equivalent[..] {
			runtime_support::with_externalities(ext, || match method {
				// TODO: Panic handler that comes back with error.
				"execute_block" => Ok(runtime::execute_block(data.0)),
				"execute_transaction" => Ok(runtime::execute_transaction(data.0)),
				_ => Err(runtime_support::NoError),//ErrorKind::MethodNotFound(method.to_owned()).into()),
			})
		} else {
			// call into wasm.
		}
	}
}
