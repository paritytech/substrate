#![cfg_attr(not(feature = "std"), no_std)]

sp_api::decl_runtime_apis! {
	/// Runtime api for testing the migration of a FRAME runtime.
	// TODO: move this to frame.
	pub trait DryRunRuntimeUpgrade {
		/// dry-run runtime upgrades, returning the total weight consumed.
		fn dry_run_runtime_upgrade() -> u64;
	}
}
