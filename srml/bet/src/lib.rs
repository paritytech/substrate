// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! The Bet: A simple Bet of a runtime module demonstrating
//! concepts, APIs and structures common to most runtime modules.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

extern crate sr_std;
#[cfg(test)] extern crate sr_io;
#[cfg(test)] extern crate substrate_primitives;
extern crate sr_primitives;
#[macro_use] extern crate parity_codec_derive;
extern crate parity_codec as codec;
#[macro_use] extern crate srml_support as support;
extern crate srml_system as system;
extern crate srml_balances as balances;

use sr_primitives::{traits::{As, One, Zero}};
use support::{StorageValue, StorageMap, Parameter, dispatch::Result};
use system::ensure_signed;
use balances::{OnFreeBalanceZero, EnsureAccountLiquid};

/// Trait for getting a price.
pub trait FetchPrice<Balance> {
	/// Fetch the price.
	fn fetch_price() -> Balance;
}

/// Our module's configuration trait.
pub trait Trait: balances::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// Get the amount of tokens worth 1 Euro.
	type OneEuro: FetchPrice<<Self as balances::Trait>::Balance>;
}

// Periods
// Block
// 0 1 2 3 4 5 6 7 8 9
// Period
// 0 0 0 1 1 1 2 2 2 3
//

#[derive(Encode, Decode, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum State<BlockNumber: Parameter> {
	Idle,
	BeganAt(BlockNumber),
	EndingAt(BlockNumber),
}
impl<BlockNumber: Parameter> Default for State<BlockNumber> {
	fn default() -> Self {
		State::Idle
	}
}

enum ConsolidatedState {
	Idle,
	JustBegan,
	AboutToEnd,
}

#[derive(Encode, Decode, Clone, Eq, PartialEq, Default)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Betting<BlockNumber: Parameter, Balance: Parameter> {
	/// Our current betting state.
	state: State<BlockNumber>,

	/// The block that we are locked until.
	locked_until: Option<BlockNumber>,

	/// The balance with which we are betting.
	balance: Balance,
}

decl_storage! {
	trait Store for Module<T: Trait> as Bet {
		/// Period in which betting happens, measured in blocks.
		Period get(period) config(): T::BlockNumber = T::BlockNumber::sa(1000);

		/// Factor controlling the attenuation speed of the target when missed.
		/// The price is reduced by a factor of one divided by this. It *must* be greater
		/// than one.
		TargetAttenuation get(target_attenuation) config(): T::Balance;

		/// The number of times to sample the spot price per period in order to determine the
		/// average price.
		Samples get(samples) config(): u64;

		/// The target price to beat.
		Target get(target) config(): T::Balance;

		/// Index of current period.
		Index get(index): T::BlockNumber;

		/// Betting information.
		Bets get(bets): map T::AccountId => Betting<T::BlockNumber, T::Balance>;

		/// This period's prices.
		Prices get(prices): Vec<T::Balance>;

		/// The pot.
		Pot get(pot): T::Balance;

		/// The cumulative amount that is staked for the next payout.
		NextTotal get(next_total): T::Balance;

		/// Payout history. Some is when there's a payout (the first parameter is the total amount
		/// that was at stake at the point of payout, the second was the pot). None is when
		/// it's a wipeout.
		Payouts get(payouts): map T::BlockNumber => Option<(T::Balance, T::Balance)>;
	}
}

decl_event!(
	pub enum Event<T> where B = <T as balances::Trait>::Balance {
		Dummy(B),
	}
);

/*
Example 1: Bet for a single period; collect-after-unlock.
				[p=0, None, None; "NULL"]
bet
				[p=0, Some(1), None; "UNLOCKED"]
period-end
				[p=1, Some(1), None; "BETTING"]
unbet
				[p=1, Some(1), Some(2); "BETTING"]
period-end
				[p=2, Some(1), Some(2); "LOCKED"]
period-end
				[p=3, Some(1), Some(2); "UNLOCKED"]
collect
				[p=4, None, None; "NULL"]

Example 2: Bet followed immediately be unbet is a no-op
				[p=0, None, None; "NULL"]
bet
				[p=0, Some(1), None; "UNLOCKED"]
unbet
				[p=0, None, None; "NULL"]
period-end
				[p=1, None, None; "NULL"]

Example 3: Double-bet/unbet is no-op
				[p=0, None, None; "NULL"]
bet
				[p=0, Some(1), None; "UNLOCKED"]
bet (no-op)
				[p=0, Some(1), None; "UNLOCKED"]
period-end
				[p=1, Some(1), None; "BETTING"]
bet (no-op)
				[p=1, Some(1), None; "BETTING"]
unbet
				[p=1, Some(1), Some(2); "BETTING"]
unbet (no-op)
				[p=1, Some(1), Some(2); "BETTING"]

Example 4: Double-bet/unbet is no-op
				[p=0, None, None; "NULL"]
bet
				[p=0, w=[], t=1, Some(1), None; "UNLOCKED"]
period-end
				[p=1, w=[N], t=0, Some(1), None; "BETTING"]
period-end
				[p=2, w=[N, 0], t=0, Some(1), None; "BETTING"]
unbet
				[p=2, w=[N, 0], t=0, Some(1), Some(3); "BETTING"]
bet
				[p=2, w=[N, 0], t=0, Some(1), None; "UNLOCKED"]
*/

// The module declaration.
decl_module! {
	// Simple declaration of the `Module` type. Lets the macro know what its working on.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		/// Add the sender to the betting system. At the next period they will be betting
		/// that the price will go up and their funds locked for at least two periods. If they
		/// are currently not active, but were, then it will issue any payouts.
		fn bet(origin) {
			let sender = ensure_signed(origin)?;
			let current = Self::index();
			let next = current + One::one();

			let balance_at_stake_is_zero = <Bets<T>>::mutate(&sender, |b| {
				let cs = Self::consolidate(&sender, b);

				// We are now guaranteed that b.state will be one of:
				// - Idle
				// - BeganAt(current)
				// - EndingAt(next)

				// Bets(sender) may no longer exist now (if our history implied we got wiped
				// out; check this and early-exit if so):
				if b.balance.is_zero() {
					return true;
				}

				match cs {
					ConsolidatedState::Idle => {
						b.state = State::BeganAt(next);
						b.balance = <balances::Module<T>>::free_balance(&sender);
					}
					ConsolidatedState::JustBegan => {
						// Already betting. Nothing to do; bail to avoid erroneously accumulating balance.
						return b.balance.is_zero()
					}
					ConsolidatedState::AboutToEnd => {
						// Scheduled to end exactly when we're meant to start again. Current period is still to 
						// be accounted for, so we reset to BeginAt the current. We can't update the balance to
						// `account_balance` since it would invalidate the current period's win calculation;
						// instead we use the old betted balance.
						b.state = State::BeganAt(current);
					}
				};

				<NextTotal<T>>::mutate(|total| *total += b.balance);
				b.balance.is_zero()
			});

			// We've been wiped out: kill entry.
			if balance_at_stake_is_zero {
				<Bets<T>>::remove(&sender)
			}
		}

		/// Remove the sender from the betting system. At the next period they will no
		/// longer be betting that the price will go up and their funds will be locked
		/// for one further period.
		fn unbet(origin) {
			let sender = ensure_signed(origin)?;

			let balance_at_stake_is_zero = <Bets<T>>::mutate(&sender, |b| {
				let cs = Self::consolidate(&sender, b);

				// We are now guaranteed that b.state will be one of:
				// - Idle
				// - BeganAt(current)
				// - EndingAt(next)

				// Bets(sender) may no longer exist now (if our history implied we got wiped
				// out; check this and early-exit if so):
				if b.balance.is_zero() {
					return true;
				}

				match cs {
					ConsolidatedState::JustBegan => {
						let next = Self::index() + One::one();
						b.state = State::EndingAt(next);
						b.locked_until = Some(next + One::one());
						<NextTotal<T>>::mutate(|total| *total -= b.balance)
					}
					_ => {}
				};
				false
			});

			// We've been wiped out: kill entry.
			if balance_at_stake_is_zero {
				<Bets<T>>::remove(&sender)
			}
		}

		/// Withdraw from the system in general. You must be past the lock period for
		/// this not to be a no-op.
		fn collect(origin) {
			let sender = ensure_signed(origin)?;

			let is_unlocked = <Bets<T>>::mutate(&sender, |b| {
				Self::consolidate(&sender, b);
				b.state == State::Idle && b.locked_until.map_or(true, |l| l <= Self::index())
			});

			if is_unlocked {
				<Bets<T>>::remove(&sender);
			}
		}

		// The signature could also look like: `fn on_finalise()`
		fn on_finalise(n: T::BlockNumber) {
			let samples = Self::samples();
			let samples_bn = T::BlockNumber::sa(samples);
			let p = Self::period();
			let mp = Self::period() / T::BlockNumber::sa(samples);
			let ph = p - One::one() - n % p;

			// For samples = 3, period = 7, mp = 2
			// n:   0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6
			// n%p: 0 1 2 3 4 5 6 0 1 2 3 4 5 6 0 1 2
			// ph:  6 5 4 3 2 1 0 6 5 4 3 2 1 0 6 5 4 
			//          +   +   *     +   +   *     +	[+: take sample, *: take sample, end period]

			if (ph % mp).is_zero() && ph / mp < samples_bn {
				// end of segment
				let one_euro = T::OneEuro::fetch_price();

				<Prices<T>>::mutate(|prices| prices.push(one_euro));

				if ph.is_zero() {
					// end of period

					let prices = <Prices<T>>::take();
					let mean = prices.iter().fold(T::Balance::default(), |total, &item| total + item) / T::Balance::sa(samples);
					if mean < Self::target() {
						let pot = <Pot<T>>::take();
						let total = Self::next_total();
						<Target<T>>::put(mean);
						<NextTotal<T>>::put(total + pot);
						// This is where the total should be expanded for contiguous betters.
						<Payouts<T>>::insert(Self::index(), (total, pot));
					} else {
						<Target<T>>::mutate(|p| *p = *p / Self::target_attenuation() * (Self::target_attenuation() + One::one()));
						<NextTotal<T>>::kill();
					}

					<Index<T>>::mutate(|i| *i += One::one());
				}
			}
		}
	}
}

impl<T: Trait> Module<T> {
	/// Contibute some funds to the pot. (It is assumed that the funds are burned elsewhere in the system.)
	pub fn contribute(value: T::Balance) {
		<Pot<T>>::mutate(|p| *p += value);
	}

	/// Consolidates the `betting` state of `who` into one of `Idle, BeganAt(Self::index()) and EndingAt(Self::index + 1)`
	/// Calling this could delete the relevant entry in `Bets`.
	fn consolidate(who: &T::AccountId, betting: &mut Betting<T::BlockNumber, T::Balance>) -> ConsolidatedState {
		let now = Self::index();
		let (new_balance, result) = match betting.state.clone() {
			State::BeganAt(n) if n < now => {
				// calculate and impose new balance implied by [n ... now)
				betting.state = State::BeganAt(now);
				(
					Self::calculate_new_balance(betting.balance, n, now),
					ConsolidatedState::JustBegan
				)
			}
			State::EndingAt(n) if n <= now => {
				// calculate new balance implied by n
				betting.state = State::Idle;
				(
					Self::calculate_new_balance(betting.balance, n, n + One::one()),
					ConsolidatedState::Idle
				)
			}
			State::BeganAt(_) => return ConsolidatedState::JustBegan,
			State::EndingAt(_) => return ConsolidatedState::AboutToEnd,
			State::Idle => return ConsolidatedState::Idle,
		};

		if betting.balance < new_balance {
			<balances::Module<T>>::increase_free_balance_creating(who, new_balance - betting.balance);
		} else {
			// this action might delete our entry in Bets (if free_balance is reduced to zero).
			// it's ok though, since mutate will write it back out with expected values.
			let _ = <balances::Module<T>>::decrease_free_balance(who, betting.balance - new_balance);
		}

		betting.balance = new_balance;
		result
	}

	/// Returns the new balance (i.e. old plus the payout reward); will be zero if there was a wipeout.
	fn calculate_new_balance(balance: T::Balance, begin: T::BlockNumber, end: T::BlockNumber) -> <T as balances::Trait>::Balance {
		if balance.is_zero() {
			// nothing to be done here
			return balance
		}
		// pay out (or wipeout) coming...
		let mut b = begin;
		let mut new_balance = balance;
		while b < end {
			// accumulate winnings
			match Self::payouts(b) {
				Some((total_stake, pot)) => {
					// A(nother) win! Accumulate.
					// TODO: check for overflow (we're assuming 32-bits at the upper end here).
					// See #935.
					let payout = ((balance >> 32) / total_stake * pot) << 32;
					new_balance += payout;
					// This is where the total should be expanded for contiguous betters.
				}
				None => {
					// wipeout.
					return Zero::zero()
				}
			}
			b += One::one();
		}
		new_balance
	}
}

impl<T: Trait> EnsureAccountLiquid<T::AccountId> for Module<T> {
	fn ensure_account_liquid(who: &T::AccountId) -> Result {
		if <Bets<T>>::exists(who) {
			Err("cannot transfer illiquid funds")
		} else {
			Ok(())
		}
	}
}

impl<T: Trait> OnFreeBalanceZero<T::AccountId> for Module<T> {
	fn on_free_balance_zero(who: &T::AccountId) {
		<Bets<T>>::remove(who);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	
	use ::std::cell::Cell;
	use sr_io::with_externalities;
	use substrate_primitives::{H256, Blake2Hasher};
	// The testing primitives are very useful for avoiding having to work with signatures
	// or public keys. `u64` is used as the `AccountId` and no `Signature`s are requried.
	use sr_primitives::{
		BuildStorage, traits::{BlakeTwo256, OnFinalise}, testing::{Digest, DigestItem, Header}
	};

	thread_local! { static ONE_EURO: Cell<u64> = Cell::new(100); }
	pub struct StaticOneEuro;
	impl FetchPrice<u64> for StaticOneEuro {
		fn fetch_price() -> u64 {
			ONE_EURO.with(|o| o.get())
		}
	}
	fn set_price(p: u64) {
		ONE_EURO.with(|o| o.set(p));
	}

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	// For testing the module, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of modules we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Header = Header;
		type Event = ();
		type Log = DigestItem;
	}
	impl balances::Trait for Test {
		type Balance = u64;
		type AccountIndex = u64;
		type OnFreeBalanceZero = ();
		type EnsureAccountLiquid = ();
		type Event = ();
	}
	impl Trait for Test {
		type Event = ();
		type OneEuro = StaticOneEuro;
	}
	type System = system::Module<Test>;
	type Balances = balances::Module<Test>;
	type Bet = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> sr_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap().0;
		// We use default for brevity, but you can configure as desired if needed.
		t.extend(balances::GenesisConfig::<Test>::default().build_storage().unwrap().0);
		t.extend(GenesisConfig::<Test>{
			period: 5,
			samples: 2,
			target_attenuation: 10,
			target: 100,
		}.build_storage().unwrap().0);
		t.into()
	}

	#[test]
	fn config_works() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Bet::period(), 5);
			assert_eq!(Bet::samples(), 2);
			assert_eq!(Bet::target_attenuation(), 10);
			assert_eq!(Bet::target(), 100);
			assert_eq!(Bet::index(), 0);
			assert_eq!(Bet::bets(0), Betting::default());
			assert_eq!(Bet::prices(), vec![]);
			assert_eq!(Bet::pot(), 0);
			assert_eq!(Bet::next_total(), 0);
			assert_eq!(Bet::payouts(0), None);
		});
	}

	#[test]
	fn price_sampling_works() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			set_price(120);
			Bet::on_finalise(System::block_number());
			assert_eq!(Bet::prices(), vec![]);

			System::set_block_number(2);
			set_price(80);
			Bet::on_finalise(System::block_number());
			assert_eq!(Bet::prices(), vec![80]);

			System::set_block_number(3);
			set_price(140);
			Bet::on_finalise(System::block_number());
			assert_eq!(Bet::prices(), vec![80]);

			System::set_block_number(4);
			set_price(100);
			Bet::on_finalise(System::block_number());
			assert_eq!(Bet::prices(), vec![]);
			assert_eq!(Bet::payouts(0), Some((0, 0)));
			assert_eq!(Bet::index(), 1);
			assert_eq!(Bet::target(), 90);
		});
	}
}
