use super::*;
use frame_support::migration::{StorageIterator, put_storage_value};
use frame_support::weights::Weight;
use sp_runtime::traits::One;

mod deprecated {
    use crate::Trait;
    use frame_support::{decl_module, decl_storage};
    use sp_std::prelude::*;

    decl_storage! {
        trait Store for Module<T: Trait> as Indices {
            /// The next free enumeration set.
            pub NextEnumSet get(fn next_enum_set): T::AccountIndex;
    
            /// The enumeration sets.
            pub EnumSet get(fn enum_set): map hasher(opaque_blake2_256) T::AccountIndex => Vec<T::AccountId>;
        }
    }
    decl_module! {
        pub struct Module<T: Trait> for enum Call where origin: T::Origin { }
    }
}

// Taken from a migration removal PR [here](https://github.com/paritytech/substrate/pull/5870/files#diff-12b2ce0dfddc1915cd81a902d368c2e7L246)
pub fn migrate_enum_set<T: Trait>() -> Weight {
    if deprecated::NextEnumSet::<T>::exists() {
        // migrations need doing.
        sp_runtime::print("🕊️  Migrating Indices...");
        let set_count = deprecated::NextEnumSet::<T>::take();
        let set_size: T::AccountIndex = 64.into();

        let mut set_index: T::AccountIndex = Zero::zero();
        while set_index < set_count {
            if !deprecated::EnumSet::<T>::contains_key(&set_index) {
                break;
            }
            let accounts = deprecated::EnumSet::<T>::take(&set_index);
            for (item_index, target) in accounts.into_iter().enumerate() {
                if target != T::AccountId::default() && !T::Currency::total_balance(&target).is_zero() {
                    let index = set_index * set_size + T::AccountIndex::from(item_index as u32);
                    // We need to add `false` to indicate the index is not frozen.
                    // See the [frozen indices PR](https://github.com/paritytech/substrate/pull/6307/)
                    Accounts::<T>::insert(index, (target, BalanceOf::<T>::zero(), false));
                }
            }
            set_index += One::one();
        }

        for (key, value) in StorageIterator::<(T::AccountId, BalanceOf<T>)>::new(b"Indices", b"Accounts").drain() {
            put_storage_value(b"Indices", b"Accounts", &key, (value.0, value.1, false));
        }
        sp_runtime::print("🕊️  Done Indices.");
        T::MaximumBlockWeight::get()
    } else {
        sp_runtime::print("🕊️  No Indices to migrate.");
        0
    }
}
