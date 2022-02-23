use sc_service::ChainType;

mod runtime {
	include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));
	/// Wasm binary unwrapped. If built with `SKIP_WASM_BUILD`, the function panics.
	pub fn wasm_binary_unwrap() -> &'static [u8] {
		WASM_BINARY.expect(
			"Development wasm binary is not available. This means the client is built with \
			 `SKIP_WASM_BUILD` flag and it is only usable for production chains. Please rebuild with \
			 the flag disabled.",
		)
	}
}

/// Specialized `ChainSpec`. This is a specialization of the general Substrate ChainSpec type.
pub type ChainSpec = sc_service::GenericChainSpec<()>;

pub fn development_config() -> Result<ChainSpec, String> {
	Ok(ChainSpec::from_runtime(
		"Development",
		"dev",
		ChainType::Development,
		runtime::wasm_binary_unwrap(),
		"Genesis_build_dev",
		vec![],
		None,
		None,
		None,
		None,
		Default::default(),
	))
}

pub fn local_testnet_config() -> Result<ChainSpec, String> {
	Ok(ChainSpec::from_runtime(
		"Local Testnet",
		"local_testnet",
		ChainType::Local,
		runtime::wasm_binary_unwrap(),
		"Genesis_build_genesis",
		vec![],
		None,
		None,
		None,
		None,
		Default::default(),
	))
}
