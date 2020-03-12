// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Temporary migrations of the balances module.

use super::*;

pub fn on_runtime_upgrade<T: Trait<I>, I: Instance>() {
	match StorageVersion::<I>::get() {
		Releases::V2_0_0 => return,
		Releases::V1_0_0 => upgrade_v1_to_v2::<T, I>(),
	}
}

// Upgrade from the pre-#4649 balances/vesting into the new balances.
fn upgrade_v1_to_v2<T: Trait<I>, I: Instance>() {
	sp_runtime::print("Upgrading account balances...");
	// First, migrate from old FreeBalance to new Account.
	// We also move all locks across since only accounts with FreeBalance values have locks.
	// FreeBalance: map T::AccountId => T::Balance
	for (hash, free) in StorageIterator::<T::Balance>::new(b"Balances", b"FreeBalance").drain() {
		let mut account = AccountData { free, ..Default::default() };
		// Locks: map T::AccountId => Vec<BalanceLock>
		let old_locks = get_storage_value::<Vec<OldBalanceLock<T::Balance, T::BlockNumber>>>(b"Balances", b"Locks", &hash);
		if let Some(locks) = old_locks {
			let locks = locks.into_iter()
				.map(|i| {
					let (result, expiry) = i.upgraded();
					if expiry != T::BlockNumber::max_value() {
						// Any `until`s that are not T::BlockNumber::max_value come from
						// democracy and need to be migrated over there.
						// Democracy: Locks get(locks): map T::AccountId => Option<T::BlockNumber>;
						put_storage_value(b"Democracy", b"Locks", &hash, expiry);
					}
					result
				})
				.collect::<Vec<_>>();
			for l in locks.iter() {
				if l.reasons == Reasons::All || l.reasons == Reasons::Misc {
					account.misc_frozen = account.misc_frozen.max(l.amount);
				}
				if l.reasons == Reasons::All || l.reasons == Reasons::Fee {
					account.fee_frozen = account.fee_frozen.max(l.amount);
				}
			}
			put_storage_value(b"Balances", b"Locks", &hash, locks);
		}
		put_storage_value(b"Balances", b"Account", &hash, account);
	}
	// Second, migrate old ReservedBalance into new Account.
	// ReservedBalance: map T::AccountId => T::Balance
	for (hash, reserved) in StorageIterator::<T::Balance>::new(b"Balances", b"ReservedBalance").drain() {
		let mut account = get_storage_value::<AccountData<T::Balance>>(b"Balances", b"Account", &hash).unwrap_or_default();
		account.reserved = reserved;
		put_storage_value(b"Balances", b"Account", &hash, account);
	}

	// Finally, migrate vesting and ensure locks are in place. We will be lazy and just lock
	// for the maximum amount (i.e. at genesis). Users will need to call "vest" to reduce the
	// lock to something sensible.
	// pub Vesting: map T::AccountId => Option<VestingSchedule>;
	for (hash, vesting) in StorageIterator::<(T::Balance, T::Balance, T::BlockNumber)>::new(b"Balances", b"Vesting").drain() {
		let mut account = get_storage_value::<AccountData<T::Balance>>(b"Balances", b"Account", &hash).unwrap_or_default();
		let mut locks = get_storage_value::<Vec<BalanceLock<T::Balance>>>(b"Balances", b"Locks", &hash).unwrap_or_default();
		locks.push(BalanceLock {
			id: *b"vesting ",
			amount: vesting.0.clone(),
			reasons: Reasons::Misc,
		});
		account.misc_frozen = account.misc_frozen.max(vesting.0.clone());
		put_storage_value(b"Vesting", b"Vesting", &hash, vesting);
		put_storage_value(b"Balances", b"Locks", &hash, locks);
		put_storage_value(b"Balances", b"Account", &hash, account);
	}

	let prefix = {
		let encoded_prefix_key_hash = b":session:keys".to_vec().encode();
		let mut h = twox_64(&encoded_prefix_key_hash[..]).to_vec();
		h.extend(&encoded_prefix_key_hash[..]);
		h
	};

	for (hash, balances) in StorageIterator::<AccountData<T::Balance>>::new(b"Balances", b"Account").drain() {
		let nonce = take_storage_value::<T::Index>(b"System", b"AccountNonce", &hash).unwrap_or_default();
		let mut refs: system::RefCount = 0;
		// The items in Kusama that would result in a ref count being incremented.
		if have_storage_value(b"Democracy", b"Proxy", &hash) { refs += 1 }
		// We skip Recovered since it's being replaced anyway.
		let mut prefixed_hash = prefix.clone();
		prefixed_hash.extend(&hash[..]);
		if have_storage_value(b"Session", b"NextKeys", &prefixed_hash) { refs += 1 }
		if have_storage_value(b"Staking", b"Bonded", &hash) { refs += 1 }
		put_storage_value(b"System", b"Account", &hash, (nonce, refs, &balances));
	}

	take_storage_value::<T::Index>(b"Balances", b"IsUpgraded", &[]);

	StorageVersion::<I>::put(Releases::V2_0_0);
}
