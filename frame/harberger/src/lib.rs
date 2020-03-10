// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
/// A runtime module template with necessary imports

/// Feel free to remove or edit this file as needed.
/// If you change the name of this file, make sure to update its references in runtime/src/lib.rs
/// If you remove this file, you can remove those references

/// For more guidance on Substrate modules, see the example module
/// https://github.com/paritytech/substrate/blob/master/srml/example/src/lib.rs
use frame_support::{
	decl_error, decl_event, decl_module, decl_storage,
	dispatch::DispatchResult,
	traits::{Currency, Get, ReservableCurrency},
};
use frame_system::{self as system, ensure_signed};
use sp_runtime::{
	traits::{SaturatedConversion, Saturating},
	Fixed64, PerThing, Perbill,
};

type BalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

pub trait PixelTrait: Encode + Decode + Default + Clone + PartialEq + core::fmt::Debug {}

/// The module's configuration trait.
pub trait Trait: frame_system::Trait {
	// TODO: Add other types and constants required configure this module.

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	type Currency: ReservableCurrency<Self::AccountId>;

	type InflationMultiplier: Get<Fixed64>;

	type RepriceDelay: Get<Self::BlockNumber>;

	type PixelType: PixelTrait;
}

#[derive(Encode, Decode, Default, Clone, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct PixelStruct<T: Trait> {
	owner: T::AccountId,
	val: T::PixelType,
	price: BalanceOf<T>,
	price_paid: BalanceOf<T>,
	price_paid_at: T::BlockNumber,
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		PriceTooLow,
		SelfBuy,
		PixelNotYours,
		NoPixel,
		TooSoonToReprice,
	}
}

// This module's storage items.
decl_storage! {
	trait Store for Module<T: Trait> as TemplateModule {
		Pixels: map hasher(blake2_256) u32 => Option<PixelStruct<T>>;
	}
}

decl_event!(
	pub enum Event<T>
	where
		AccountId = <T as frame_system::Trait>::AccountId,
	{
		Dummy(AccountId),
	}
);

fn inflation_multiplier<T: Trait>(price: BalanceOf<T>, price_paid_at: T::BlockNumber) -> Fixed64{
	use std::convert::TryInto;
	T::InflationMultiplier::get()
}

fn inflation_slash_amount<T: Trait>(
	price: BalanceOf<T>,
	price_paid: BalanceOf<T>,
	price_paid_at: T::BlockNumber,
) -> BalanceOf<T> {
    let multi: Fixed64 = dbg!(inflation_multiplier::<T>(price, price_paid_at));
	let mut new_price = price;
	let current_block = <system::Module<T>>::block_number();
	let blocks_passed = current_block - price_paid_at;
	for _ in 0..blocks_passed.saturated_into() {
		new_price = multi.saturated_multiply_accumulate(new_price);
	}
	dbg!(new_price - price)
}

// The module's dispatchable functions.
decl_module! {
	/// The module declaration.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		// Initializing events
		// this is needed only if you are using events in your module
		fn deposit_event() = default;

		fn on_initialize(n: T::BlockNumber) {
		}

		fn buy_pixel(origin, pixel_id: u32, price: u32) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let block_num = <system::Module<T>>::block_number();
			match Pixels::<T>::get(pixel_id) {
				None => {
					T::Currency::reserve(&who, price.into())?;
					let pixel = PixelStruct {
						owner: who.clone(),
						val: T::PixelType::default(),
						price: price.into(),
						price_paid: price.into(),
						price_paid_at: block_num,
					};
					Pixels::<T>::insert(pixel_id, pixel);
				},
				Some(mut pixel) => {
					if pixel.owner == who {
						Err(Error::<T>::SelfBuy)?;
					}

					let price_bal: BalanceOf<T> = price.into();
					if price_bal > pixel.price {

						T::Currency::reserve(&who, price.into())?;

						let slash_amount = inflation_slash_amount::<T>(
							pixel.price,
							pixel.price_paid,
							pixel.price_paid_at,
						);
						T::Currency::unreserve(
							&pixel.owner,
							pixel.price_paid.saturating_sub(slash_amount),
						);
						T::Currency::slash_reserved(
							&pixel.owner,
							slash_amount,
						);

						pixel.owner = who.clone();
						pixel.price = price.into();
						pixel.price_paid = price.into();
						pixel.price_paid_at = block_num;

						Pixels::<T>::insert(pixel_id, pixel);
					} else {
						Err(Error::<T>::PriceTooLow)?;
					}
				}
			}
			Ok(())
		}

		fn set_pixel(origin, pixel_id: u32, val: T::PixelType) -> DispatchResult {
			let who = ensure_signed(origin)?;
			match Pixels::<T>::get(pixel_id) {
				None => Err(Error::<T>::NoPixel)?,
				Some(mut pixel) => {
					if pixel.owner != who {
						Err(Error::<T>::PixelNotYours)?;
					}
					pixel.val = val;
					Pixels::<T>::insert(pixel_id, pixel);
				}
			}
			Ok(())
		}

		fn reprice_pixel(origin, pixel_id: u32, price: u32) -> DispatchResult {
			let who = ensure_signed(origin)?;
			match Pixels::<T>::get(pixel_id) {
				None => Err(Error::<T>::NoPixel)?,
				Some(mut pixel) => {

					if pixel.owner != who {
						Err(Error::<T>::PixelNotYours)?;
					}

					let block_num = <system::Module<T>>::block_number();
					if block_num < pixel.price_paid_at + T::RepriceDelay::get().into() {
						Err(Error::<T>::TooSoonToReprice)?;
					}

					let slash_amount = inflation_slash_amount::<T>(
						pixel.price,
						pixel.price_paid,
						pixel.price_paid_at,
					);
                    T::Currency::slash_reserved(
                        &pixel.owner,
                        slash_amount,
                    );

                    dbg!(&pixel.price_paid);
                    dbg!(&slash_amount);
					pixel.price = price.into();
					let reserve_remaining = pixel.price_paid - slash_amount;
                    dbg!(&reserve_remaining);
					pixel.price_paid = reserve_remaining;
					pixel.price_paid_at = block_num;

					Pixels::<T>::insert(pixel_id, pixel);
				}
			}
			Ok(())
		}
	}
}

/// tests for this module
#[cfg(test)]
mod tests {
	use super::*;

	use frame_support::{assert_ok, impl_outer_origin, parameter_types, weights::Weight};
	use sp_core::H256;
	use sp_runtime::{
		testing::Header,
		traits::{BlakeTwo256, IdentityLookup, OnFinalize, OnInitialize},
		Perbill,
	};

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	// For testing the module, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of modules we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::from_percent(75);
	}
	impl frame_system::Trait for Test {
		type Origin = Origin;
		type Call = ();
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
		type ModuleToIndex = ();
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
	}
	impl Trait for Test {
		type Event = ();
		type Currency = Balances;
		type RepriceDelay = RepriceDelay;
		type InflationMultiplier = InflationMultiplier;
		type PixelType = PixelTestStruct;
	}

	#[derive(Encode, Decode, Clone, PartialEq, Debug)]
	pub struct PixelTestStruct {}
	impl Default for PixelTestStruct {
		fn default() -> Self {
			PixelTestStruct {}
		}
	}
	impl PixelTrait for PixelTestStruct {}

	parameter_types! {
		pub const ExistentialDeposit: u64 = 1;
		pub const RepriceDelay: u64 = 1;
		pub const InflationMultiplier: Fixed64 = Fixed64::from_rational(1, 10);
		pub const PixelType: PixelTestStruct = PixelTestStruct {};
	}
	impl pallet_balances::Trait for Test {
		type Balance = u64;
		type Event = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
	}

	type System = frame_system::Module<Test>;
	type Balances = pallet_balances::Module<Test>;
	type PixelsModule = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default()
			.build_storage::<Test>()
			.unwrap();
		pallet_balances::GenesisConfig::<Test> {
			balances: vec![(1, 100), (2, 100), (3, 100), (4, 100), (5, 100)],
		}
		.assimilate_storage(&mut t)
		.unwrap();
		t.into()
	}

	#[test]
	fn test_buy_pixel() {
		new_test_ext().execute_with(|| {
			// Just a dummy test for the dummy funtion `do_something`
			// calling the `do_something` function with a value 42
			assert_ok!(PixelsModule::buy_pixel(Origin::signed(1), 42, 1));
			// asserting that the stored value is equal to what we stored
			assert!(Pixels::<Test>::get(41).is_none());
			assert!(Pixels::<Test>::get(42).is_some());
			// can't buy for the same price
			assert!(PixelsModule::buy_pixel(Origin::signed(1), 42, 1).is_err());
			// can't buy off yourself
			assert!(PixelsModule::buy_pixel(Origin::signed(1), 42, 2).is_err());
			// someone new can buy for a higher price
			assert_ok!(PixelsModule::buy_pixel(Origin::signed(2), 42, 2));
		});
	}

	#[test]
	fn test_set_pixel() {
		new_test_ext().execute_with(|| {
			assert!(
				PixelsModule::set_pixel(Origin::signed(1), 42, PixelTestStruct::default()).is_err()
			);
			assert_ok!(PixelsModule::buy_pixel(Origin::signed(1), 42, 1));
			assert_ok!(PixelsModule::set_pixel(
				Origin::signed(1),
				42,
				PixelTestStruct::default()
			));
			assert!(
				PixelsModule::set_pixel(Origin::signed(2), 42, PixelTestStruct::default()).is_err()
			);
		});
	}

	/// Run until a particular block.
	pub fn run_to_block(n: u64) {
		while System::block_number() < n {
			if System::block_number() > 1 {
				System::on_finalize(System::block_number());
			}
			System::set_block_number(System::block_number() + 1);
			System::on_initialize(System::block_number());
		}
	}

	#[test]
	fn test_reprice_pixel() {
		new_test_ext().execute_with(|| {
            let origin = Origin::signed(1);
            let pixel = 42;
            let price0 = 100;
            let price1 = 50;

            // err: pixel unowned
			assert!(PixelsModule::reprice_pixel(origin.clone(), pixel, price0).is_err()); 			

            // ok
            assert_ok!(PixelsModule::buy_pixel(origin.clone(), pixel, price0));
            assert_eq!(<system::Module<Test>>::block_number(), 1u64.into());
			run_to_block(3);

            // ok
			assert_ok!(PixelsModule::reprice_pixel(origin.clone(), pixel, price1));

            // err: too soon to reprice
			assert!(PixelsModule::reprice_pixel(origin.clone(), pixel, price0).is_err());
		})
	}
}
