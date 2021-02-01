#![feature(prelude_import)]
#[prelude_import]
use std::prelude::v1::*;
#[macro_use]
extern crate std;
#[doc(hidden)]
mod sp_api_hidden_includes_DECL_RUNTIME_APIS {
    pub extern crate sp_api as sp_api;
}
#[doc(hidden)]
#[allow(dead_code)]
#[allow(deprecated)]
pub mod runtime_decl_for_DryRunRuntimeUpgrade {
    use super::*;
    /// Runtime api for benchmarking a FRAME runtime.
    pub trait DryRunRuntimeUpgrade<
        Block: self::sp_api_hidden_includes_DECL_RUNTIME_APIS::sp_api::BlockT,
    >
    {
        /// Dispatch the given benchmark.
        fn dry_run_runime_upgrade() -> u64;
    }
    pub const VERSION: u32 = 1u32;
    pub const ID: [u8; 8] = [184u8, 6u8, 13u8, 174u8, 117u8, 5u8, 75u8, 81u8];
}
