use super::*;
use frame_support::weights::Weight;
use sp_runtime::traits::SaturatedConversion;

pub fn migrate<T: Trait>() -> Weight{
	migrate_block_hash::<T>()
}

pub fn migrate_block_hash<T: Trait>() -> Weight {
	// Number is current block - we obviously don't know that hash.
	// Number - 1 is the parent block, who hash we record in this block, but then that's already
	//  with the new storage so we don't migrate it.
	// Number - 2 is therefore the most recent block's hash that needs migrating.
	let db = T::DbWeight::get();
	let block_num = Number::<T>::get();
	frame_support::runtime_print!("BlockNumber: {}", block_num.saturated_into::<u64>());
	if block_num > One::one() {
		sp_runtime::print("🕊️  Migrating BlockHashes...");
		BlockHash::<T>::migrate_key_from_blake(T::BlockNumber::zero());
		let mut n = block_num - One::one() - One::one();
		let mut migrations = 1;
		while !n.is_zero() {
			migrations += 1;
			if BlockHash::<T>::migrate_key_from_blake(n).is_none() {
				break;
			}
			n -= One::one();
		}
		sp_runtime::print("🕊️  Done BlockHashes");
		db.reads_writes(migrations + 1, migrations)
	} else {
		sp_runtime::print("🕊️  No BlockHashes to migrate...");
		db.reads(1)
	}
}

pub fn migrate_accounts<T: Trait>() -> Weight {
	sp_runtime::print("🕊️  Migrating Accounts...");
	let mut count = 0u32;
	if let Ok(accounts) = Vec::<T::AccountId>::decode(&mut &include_bytes!("accounts.scale")[..]) {
		for a in &accounts {
			if Account::<T>::migrate_key_from_blake(a).is_some() {
				// Inform other modules about the account.
				T::MigrateAccount::migrate_account(a);
				count += 1;
				if count % 1000 == 0 {
					sp_runtime::print(count);
				}
			}
		}
	}
	sp_runtime::print(count);
	sp_runtime::print("🕊️  Done Accounts.");
	T::MaximumBlockWeight::get()
}