mod linked_map;
mod map;
mod double_map;
mod value;

pub use linked_map::StorageLinkedMap;
pub use map::StorageMap;
pub use double_map::StorageDoubleMap;
pub use value::StorageValue;

// TODO TODO: just maybe reduce the scope of the PR because of storage_item macro:
// * remove generator
// * move linkedmap to its own trait
// * storage items impls directly main trait
// * decl_storage use new generators
//
// finally this is fine just do storage_items impls directly into main trait.
// also we can still used hashed storage here instead of using only unhashed. but OK
