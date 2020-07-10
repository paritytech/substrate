use super::*;
use frame_support::migration::{StorageIterator, put_storage_value};

// Migration necessary for the Edgeware migration.
// Created in the [stacked filtering PR](https://github.com/paritytech/substrate/pull/6273/files#diff-9967c6d85464599e91d4626b3869c66bR209)
// and removed [here](https://github.com/paritytech/substrate/pull/6476/files#diff-9967c6d85464599e91d4626b3869c66bL238)
pub fn migrate_utility_to_multisigs<T: Trait>() -> Weight {
    // Utility.Multisigs -> Multisig.Multisigs
    sp_runtime::print("🕊️  Migrating Multisigs...");
    for (key, value) in StorageIterator::<
        Multisig<T::BlockNumber, BalanceOf<T>, T::AccountId>
    >::new(b"Utility", b"Multisigs").drain() {
        put_storage_value(b"Multisig", b"Multisigs", &key, value);
    }
    sp_runtime::print("🕊️  Done Multisigs.");
    1_000_000_000
}
