use super::*;
use hex_literal::hex;
use sp_runtime::traits::SaturatedConversion;

pub fn migrate<T: Trait>() {

	// Number is current block - we obviously don't know that hash.
	// Number - 1 is the parent block, who hash we record in this block, but then that's already
	//  with the new storage so we don't migrate it.
	// Number - 2 is therefore the most recent block's hash that needs migrating.
	if Number::<T>::get() > One::one() {
		sp_runtime::print("Migrating BlockHash...");
		let mut n = Number::<T>::get() - One::one() - One::one();
		while !n.is_zero() {
			sp_runtime::print(n.saturated_into::<u32>());
			if BlockHash::<T>::migrate_key_from_blake(n).is_none() {
				break;
			}
			n -= One::one();
		}
	}

	sp_runtime::print("Migrating Accounts...");
//	let accounts = include!("accountids.rs");
	let accounts = [
		hex!["86b7409a11700afb027924cb40fa43889d98709ea35319d48fea85dd35004e64"],
		hex!["bef3f1aa71b32bba775b3886b900a2e3fb4f4163d58c1bce0aaecfe0b55c1b5f"],
	];
	let mut count = 0u32;
	for a in accounts.iter().filter_map(|a| T::AccountId::decode(&mut &a[..]).ok()) {
		if Account::<T>::migrate_key_from_blake(&a).is_some() {
			// Inform other modules about the account.
			T::MigrateAccount::migrate_account(&a);
			count += 1;
			if count % 1000 == 0 {
				sp_runtime::print(count);
			}
		}
	}
	sp_runtime::print(count);
}
