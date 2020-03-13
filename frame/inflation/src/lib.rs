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
	traits::SaturatedConversion,
	Perbill, PerThing,
};

const INFLATION_BASE: u32 = 2;
type BalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as frame_system::Trait>::AccountId>>::Balance;

pub trait PixelTrait: Encode + Decode + Default + Clone + PartialEq + core::fmt::Debug {}

/// The module's configuration trait.
pub trait Trait: frame_system::Trait + Default {
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;
	type Currency: ReservableCurrency<Self::AccountId>;
	type RepriceDelay: Get<Self::BlockNumber>;
	type PixelType: PixelTrait;
}

#[derive(Encode, Decode, Default, Clone, PartialEq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct PixelStruct<T: Trait> {
	owner: T::AccountId,
	val: T::PixelType,
	rate_sig: Perbill,
	rate_exp: u32,
	reserve: BalanceOf<T>,
	reserved_at: T::BlockNumber,
}

decl_error! {
	pub enum Error for Module<T: Trait> {
		PriceTooLow,
		SelfBuy,
		PixelNotYours,
		NoPixel,
		TooSoonToReprice,
		NoReserveRemaining,
	}
}

// This module's storage items.
decl_storage! {
	trait Store for Module<T: Trait> as TemplateModule {
		Pixels: map hasher(blake2_256) u32 => Option<PixelStruct<T>>;
        ExchangeSignificand: Perbill;
        ExchangeExponent: u32;
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

// The module's dispatchable functions.
decl_module! {
	/// The module declaration.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		// Initializing events
		// this is needed only if you are using events in your module
		fn deposit_event() = default;

		fn on_initialize(_n: T::BlockNumber) {}

		fn buy_pixel(
            origin, 
            pixel_id: u32, 
            rate_sig: Perbill, 
            rate_exp: u32, 
            reserve: BalanceOf<T>
        ) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let block_num = <system::Module<T>>::block_number();
			match Pixels::<T>::get(pixel_id) {
				None => {
					T::Currency::reserve(&who, reserve)?;
					let pixel = PixelStruct {
						owner: who.clone(),
						val: T::PixelType::default(),
						rate_sig: rate_sig,
                        rate_exp: rate_exp,
						reserve: reserve,
						reserved_at: block_num,
					};
					Pixels::<T>::insert(pixel_id, pixel);
				},
				Some(mut pixel) => {
					if pixel.owner == who {
						Err(Error::<T>::SelfBuy)?;
					}

                    let owner_value_remaining = {
                        let blocks_passed = (block_num - pixel.reserved_at).saturated_into::<u32>();
                        let mut x = pixel.reserve;
                        for _ in 0..blocks_passed {
                            x *= 1_000_000_000.into();
                            x /= pixel.rate_sig.deconstruct().into();
                            x /= INFLATION_BASE.pow(pixel.rate_exp).into();
                        }
                        x
                    };

                    if owner_value_remaining == 0.into() {
                        T::Currency::reserve(&who, reserve)?;
                        let pixel = PixelStruct {
                            owner: who.clone(),
                            val: T::PixelType::default(),
                            rate_sig: rate_sig,
                            rate_exp: rate_exp,
                            reserve: reserve,
                            reserved_at: block_num,
                        };
                        Pixels::<T>::insert(pixel_id, pixel);
                    } else if rate_exp > pixel.rate_exp || (rate_exp == pixel.rate_exp && rate_sig > pixel.rate_sig) {
                        T::Currency::reserve(&who, reserve)?;
                        T::Currency::unreserve(
                            &pixel.owner,
                            owner_value_remaining.into(),
                        );
                        T::Currency::slash_reserved(
                            &pixel.owner,
                            pixel.reserve - owner_value_remaining,
                        );

                        pixel.owner = who.clone();
                        pixel.rate_sig = rate_sig;
                        pixel.rate_exp = rate_exp;
                        pixel.reserve = reserve;
                        pixel.reserved_at = block_num;
                        Pixels::<T>::insert(pixel_id, pixel);
                    } else {
                        Err(Error::<T>::PriceTooLow)?;
                    }
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

	use frame_support::{assert_ok, assert_err, impl_outer_origin, parameter_types, weights::Weight};
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
	#[derive(Default, Clone, Eq, PartialEq)]
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
		pub const PixelType: PixelTestStruct = PixelTestStruct::default();
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
			balances: vec![(1, 1000), (2, 1000), (3, 1000), (4, 1000), (5, 1000)],
		}
		.assimilate_storage(&mut t)
		.unwrap();
		t.into()
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
	fn test_buy_pixel() {
		new_test_ext().execute_with(|| {
			assert_ok!(
                PixelsModule::buy_pixel(
                    Origin::signed(1), 
                    42, 
                    Perbill::from_percent(55), 
                    1, 
                    100
                    )
                );
			assert!(Pixels::<Test>::get(41).is_none());
			assert!(Pixels::<Test>::get(42).is_some());
			// can't buy for the same price
			assert_err!(
                PixelsModule::buy_pixel(
                    Origin::signed(2), 
                    42, 
                    Perbill::from_percent(55), 
                    1, 
                    100
                    ),
                    Error::<Test>::PriceTooLow
                );
			// can't buy off yourself
			assert_err!(
                PixelsModule::buy_pixel(
                    Origin::signed(1), 
                    42, 
                    Perbill::from_percent(60), 
                    1, 
                    100
                    ),
                    Error::<Test>::SelfBuy
                );
			// someone new can buy for a higher price (rate significand)
			assert_ok!(
                PixelsModule::buy_pixel(
                    Origin::signed(3), 
                    42, 
                    Perbill::from_percent(60), 
                    1, 
                    100
                    )
                );
			// someone new can buy for a higher price (rate exponent)
			assert_ok!(
                PixelsModule::buy_pixel(
                    Origin::signed(4), 
                    42, 
                    Perbill::from_percent(55), 
                    2, 
                    100
                    )
                );
        }

        #[test]
        fn test_inflation() {
			assert_ok!(
                PixelsModule::buy_pixel(
                    Origin::signed(1), 
                    42, 
                    // with rate_exp=1 this is 10% inflation per block
                    Perbill::from_percent(55), 
                    1, 
                    100
                    )
                );
            // can't buy at a lower price while owner has reserve remaining
            run_to_block(30);
			assert_err!(
                PixelsModule::buy_pixel(
                    Origin::signed(2), 
                    42, 
                    Perbill::from_percent(51), 
                    1, 
                    100
                    ),
                    Error::<Test>::PriceTooLow
                );

            // someone new can buy at any price once the owner's reserve is worthless
            run_to_block(31);
			assert_ok!(
                PixelsModule::buy_pixel(
                    Origin::signed(2), 
                    42, 
                    Perbill::from_percent(51), 
                    1, 
                    100
                    )
                );

		});
	}

    /*
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
			run_to_block(200);
			assert!(
				PixelsModule::set_pixel(Origin::signed(1), 42, PixelTestStruct::default()).is_err()
			);
		});
	}

	#[test]
	fn test_reprice_pixel() {
		new_test_ext().execute_with(|| {
			let origin = Origin::signed(1);
			let pixel = 42;
			let price0 = 100;
			let price1 = 200;

			// err: pixel unowned
			assert!(PixelsModule::reprice_pixel(origin.clone(), pixel, price0).is_err());

			// ok
			assert_ok!(PixelsModule::buy_pixel(origin.clone(), pixel, price0));
			assert_eq!(<system::Module<Test>>::block_number(), 1u64.into());
			run_to_block(3);

			// ok
			assert_ok!(PixelsModule::reprice_pixel(origin.clone(), pixel, price1));
			run_to_block(5);

			// ok
			assert_ok!(PixelsModule::reprice_pixel(origin.clone(), pixel, price0));
			run_to_block(20);

			// ok
			assert!(PixelsModule::reprice_pixel(origin.clone(), pixel, price1).is_err());

			// err: too soon to reprice
			assert!(PixelsModule::reprice_pixel(origin.clone(), pixel, price0).is_err());
		})
	}
    */
}
