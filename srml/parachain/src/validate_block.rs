use crate::ParachainBlock;
use runtime_primitives::traits::{Block as BlockT, One, Header as HeaderT};
use rstd::{vec::Vec, collections::btree_map::BTreeMap, slice, ptr};
use codec::Decode;
use executive::ExecuteBlock;

static mut STORAGE: Option<BTreeMap<Vec<u8>, Vec<u8>>> = None;

unsafe fn ext_get_allocated_storage(key_data: *const u8, key_len: u32, written_out: *mut u32) -> *mut u8 {
	let key = slice::from_raw_parts(key_data, key_len as usize);
	match STORAGE.as_mut().expect("`STORAGE` needs to be set before calling this function.").get_mut(key) {
		Some(value) => {
			*written_out = value.len() as u32;
			value.as_mut_ptr()
		},
		None => {
			*written_out = u32::max_value();
			ptr::null_mut()
		}
	}
}

unsafe fn ext_set_storage(key_data: *const u8, key_len: u32, value_data: *const u8, value_len: u32) {
	let key = slice::from_raw_parts(key_data, key_len as usize);
	let value = slice::from_raw_parts(value_data, value_len as usize);

	STORAGE.as_mut().map(|s| {
		s.insert(key.to_vec(), value.to_vec());
	});
}

/// Validate a given parachain block on a validator.
pub fn validate_block<Block: BlockT, E: ExecuteBlock<Block>>(mut block: &[u8], mut prev_head: &[u8]) {
	let block = ParachainBlock::<Block>::decode(&mut block).expect("Could not decode parachain block.");
	let parent_header = <<Block as BlockT>::Header as Decode>::decode(&mut prev_head).expect("Could not decode parent header.");

	let _guard = unsafe {
		STORAGE = Some(block.witness_data);
		(
			// Let all extern functions throw `unimplemented` when being called.
			rio::switch_extern_functions_to_unimplemented(),
			rio::ext_get_allocated_storage.replace_implementation(ext_get_allocated_storage),
			rio::ext_set_storage.replace_implementation(ext_set_storage)
		)
	};

	let block_number = *parent_header.number() + One::one();
	E::execute_extrinsics_without_checks(block_number, block.extrinsics);
}