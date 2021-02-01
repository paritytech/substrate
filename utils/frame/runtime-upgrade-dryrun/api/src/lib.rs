sp_api::decl_runtime_apis! {
	/// Runtime api for benchmarking a FRAME runtime.
	pub trait DryRunRuntimeUpgrade {
		/// Dispatch the given benchmark.
		fn dry_run_runime_upgrade() -> u64;
	}
}
