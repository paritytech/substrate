use crate::ParachainBlock;

use rio::{twox_128, TestExternalities};
use keyring::Keyring;
use primitives::map;
use runtime_primitives::traits::Block as BlockT;
use executor::{WasmExecutor, error::Result, wasmi::RuntimeValue::{I64, I32}};
use test_runtime::{Block, Header};

use std::collections::BTreeMap;

use codec::{KeyedVec, Encode};

const WASM_CODE: &'static [u8] =
	include_bytes!("../../../core/test-runtime/wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm");

fn create_witness_data() -> BTreeMap<Vec<u8>, Vec<u8>> {
	map![
		twox_128(&Keyring::Alice.to_raw_public().to_keyed_vec(b"balance:")).to_vec() => vec![111u8, 0, 0, 0, 0, 0, 0, 0]
	]
}

fn call_validate_block(block: ParachainBlock<Block>, prev_header: <Block as BlockT>::Header) -> Result<()> {
	let mut ext = TestExternalities::default();
	WasmExecutor::new().call_with_custom_signature(
		&mut ext,
		8,
		&WASM_CODE,
		"validate_block",
		|alloc| {
			let block = block.encode();
			let prev_header = prev_header.encode();
			let block_offset = alloc(&block)?;
			let prev_head_offset = alloc(&prev_header)?;

			Ok(
				vec![
					I32(block_offset as i32),
					I64(block.len() as i64),
					I32(prev_head_offset as i32),
					I64(prev_header.len() as i64),
				]
			)
		},
		|res, _| {
			if res.is_none() {
				Ok(Some(()))
			} else {
				Ok(None)
			}
		}
	)
}

#[test]
fn validate_block_with_empty_block() {
	let prev_header = Header {
		parent_hash: Default::default(),
		number: 1,
		state_root: Default::default(),
		extrinsics_root: Default::default(),
		digest: Default::default(),
	};
	call_validate_block(ParachainBlock::default(), prev_header).expect("Calls `validate_block`");
}