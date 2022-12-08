// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Test environment for Nfts pallet.

use super::*;
use crate as pallet_nfts;

use codec::MaxEncodedLen;
use frame_support::{
	construct_runtime,
	dispatch::DispatchResult,
	parameter_types,
	traits::{
		fungible::{Inspect as InspectFungible, Transfer as TransferFungible},
		fungibles::{Inspect as InspectFungibles, Transfer as TransferFungibles},
		AsEnsureOriginWithArg, Balance as BalanceTrait, ConstU32, ConstU64,
		Currency as PalletCurrency, ExistenceRequirement,
	},
	PalletId,
};
use scale_info::TypeInfo;
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		Assets: pallet_assets,
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		Nfts: pallet_nfts::{Pallet, Call, Storage, Event<T>},
	}
);

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

impl pallet_balances::Config for Test {
	type Balance = u64;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
	type MaxLocks = ();
	type MaxReserves = ConstU32<50>;
	type ReserveIdentifier = [u8; 8];
}

use pallet_assets::FrozenBalance;
pub struct TestFreezer;
impl FrozenBalance<u32, u64, u64> for TestFreezer {
	fn frozen_balance(_asset: u32, _who: &u64) -> Option<u64> {
		None
	}
	fn died(_asset: u32, _who: &u64) {}
}
impl pallet_assets::Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type Balance = u64;
	type AssetId = u32;
	type Currency = Balances;
	type CreateOrigin = AsEnsureOriginWithArg<frame_system::EnsureSigned<u64>>;
	type ForceOrigin = frame_system::EnsureRoot<u64>;
	type AssetDeposit = ConstU64<1>;
	type AssetAccountDeposit = ConstU64<10>;
	type MetadataDepositBase = ConstU64<1>;
	type MetadataDepositPerByte = ConstU64<1>;
	type ApprovalDeposit = ConstU64<1>;
	type StringLimit = ConstU32<50>;
	type Freezer = TestFreezer;
	type WeightInfo = ();
	type Extra = ();
	type RemoveItemsLimit = ConstU32<5>;
}

parameter_types! {
	pub storage Features: PalletFeatures = PalletFeatures::all_enabled();
	pub const NftsPalletId: PalletId = PalletId(*b"py/nfts_");
}

#[derive(
	Copy,
	Clone,
	Encode,
	Decode,
	Eq,
	PartialEq,
	PartialOrd,
	Ord,
	RuntimeDebug,
	TypeInfo,
	MaxEncodedLen,
)]
pub enum MultiBalance<Balance, AssetId> {
	Native(Balance),
	Asset(AssetId, Balance),
}

impl<B, AI> MultiBalance<B, AI> {
	fn balance(self) -> B {
		match self {
			Self::Native(amount) => amount,
			Self::Asset(_, amount) => amount,
		}
	}
	fn update_balance(self, new_balance: B) -> Self {
		match self {
			Self::Native(_) => Self::Native(new_balance),
			Self::Asset(id, _) => Self::Asset(id, new_balance),
		}
	}
}

impl<B: Zero, AI> Default for MultiBalance<B, AI> {
	fn default() -> Self {
		MultiBalance::zero()
	}
}

// u8.into() => MultiBalance
impl<B: From<u8>, AI> From<u8> for MultiBalance<B, AI> {
	fn from(amount: u8) -> Self {
		Self::Native(amount.into())
	}
}
impl<B: From<u16>, AI> From<u16> for MultiBalance<B, AI> {
	fn from(amount: u16) -> Self {
		Self::Native(amount.into())
	}
}
impl<B: From<u32>, AI> From<u32> for MultiBalance<B, AI> {
	fn from(amount: u32) -> Self {
		Self::Native(amount.into())
	}
}
impl<B: TryFrom<u64>, AI> TryFrom<u64> for MultiBalance<B, AI> {
	type Error = ();

	fn try_from(amount: u64) -> Result<Self, Self::Error> {
		Ok(Self::Native(amount.try_into().map_err(|_| ())?))
	}
}
impl<B: TryFrom<u128>, AI> TryFrom<u128> for MultiBalance<B, AI> {
	type Error = ();

	fn try_from(amount: u128) -> Result<Self, Self::Error> {
		Ok(Self::Native(amount.try_into().map_err(|_| ())?))
	}
}
impl<B: TryFrom<usize>, AI> TryFrom<usize> for MultiBalance<B, AI> {
	type Error = ();

	fn try_from(amount: usize) -> Result<Self, Self::Error> {
		Ok(Self::Native(amount.try_into().map_err(|_| ())?))
	}
}

// MultiBalance::Native(123456).into() => u8
impl<B: TryInto<u8>, AI> TryInto<u8> for MultiBalance<B, AI> {
	type Error = ();

	fn try_into(self) -> Result<u8, Self::Error> {
		match self {
			Self::Native(amount) => amount.try_into().map_err(|_| ()),
			Self::Asset(_, amount) => amount.try_into().map_err(|_| ()),
		}
	}
}
impl<B: TryInto<u16>, AI> TryInto<u16> for MultiBalance<B, AI> {
	type Error = ();

	fn try_into(self) -> Result<u16, Self::Error> {
		match self {
			Self::Native(amount) => amount.try_into().map_err(|_| ()),
			Self::Asset(_, amount) => amount.try_into().map_err(|_| ()),
		}
	}
}
impl<B: TryInto<u32>, AI> TryInto<u32> for MultiBalance<B, AI> {
	type Error = ();

	fn try_into(self) -> Result<u32, Self::Error> {
		match self {
			Self::Native(amount) => amount.try_into().map_err(|_| ()),
			Self::Asset(_, amount) => amount.try_into().map_err(|_| ()),
		}
	}
}
impl<B: TryInto<u64>, AI> TryInto<u64> for MultiBalance<B, AI> {
	type Error = ();

	fn try_into(self) -> Result<u64, Self::Error> {
		match self {
			Self::Native(amount) => amount.try_into().map_err(|_| ()),
			Self::Asset(_, amount) => amount.try_into().map_err(|_| ()),
		}
	}
}
impl<B: TryInto<u128>, AI> TryInto<u128> for MultiBalance<B, AI> {
	type Error = ();

	fn try_into(self) -> Result<u128, Self::Error> {
		match self {
			Self::Native(amount) => amount.try_into().map_err(|_| ()),
			Self::Asset(_, amount) => amount.try_into().map_err(|_| ()),
		}
	}
}
impl<B: TryInto<usize>, AI> TryInto<usize> for MultiBalance<B, AI> {
	type Error = ();

	fn try_into(self) -> Result<usize, Self::Error> {
		match self {
			Self::Native(amount) => amount.try_into().map_err(|_| ()),
			Self::Asset(_, amount) => amount.try_into().map_err(|_| ()),
		}
	}
}
use num_traits::{
	CheckedAdd, CheckedDiv, CheckedMul, CheckedRem, CheckedShl, CheckedShr, CheckedSub, Num, One,
	Unsigned, Zero,
};
use sp_runtime::traits::{Bounded, IntegerSquareRoot};
use sp_std::ops::{
	Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Shl, Shr, Sub, SubAssign,
};
impl<
		B: PartialEq + Zero + One + Sub<Output = B> + Rem<Output = B> + Div<Output = B>,
		AI: PartialEq,
	> Unsigned for MultiBalance<B, AI>
{
}
impl<
		B: PartialEq + Zero + One + Sub<Output = B> + Rem<Output = B> + Div<Output = B>,
		AI: PartialEq,
	> Num for MultiBalance<B, AI>
{
	type FromStrRadixErr = ();
	fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
		Err(()) // TODO: return smth like "Unsupported"
	}
}
impl<B: Add<Output = B>, AI> Add for MultiBalance<B, AI> {
	type Output = Self;
	fn add(self, other: Self) -> Self {
		self.update_balance(self.balance() + other.balance())
	}
}
impl<B: Add<Output = B>, AI> AddAssign for MultiBalance<B, AI> {
	fn add_assign(&mut self, other: Self) {
		*self = self.update_balance(self.balance() + other.balance())
	}
}
impl<B: CheckedAdd + Clone, AI> CheckedAdd for MultiBalance<B, AI> {
	fn checked_add(&self, other: &Self) -> Option<Self> {
		<B>::checked_add(&self.balance().clone(), &other.balance().clone())
			.map(|new_balance| self.update_balance(new_balance))
	}
}

impl<B: Sub<Output = B>, AI> Sub for MultiBalance<B, AI> {
	type Output = Self;
	fn sub(self, other: Self) -> Self {
		self.update_balance(self.balance() - other.balance())
	}
}
impl<B: Sub<Output = B>, AI> SubAssign for MultiBalance<B, AI> {
	fn sub_assign(&mut self, other: Self) {
		*self = self.update_balance(self.balance() - other.balance())
	}
}
impl<B: CheckedSub + Clone, AI> CheckedSub for MultiBalance<B, AI> {
	fn checked_sub(&self, other: &Self) -> Option<Self> {
		<B>::checked_sub(&self.balance().clone(), &other.balance().clone())
			.map(|new_balance| self.update_balance(new_balance))
	}
}

impl<B: Mul<Output = B>, AI> Mul for MultiBalance<B, AI> {
	type Output = Self;
	fn mul(self, other: Self) -> Self {
		self.update_balance(self.balance() * other.balance())
	}
}
impl<B: Mul<Output = B>, AI> MulAssign for MultiBalance<B, AI> {
	fn mul_assign(&mut self, other: Self) {
		*self = self.update_balance(self.balance() * other.balance())
	}
}
impl<B: CheckedMul + Clone, AI> CheckedMul for MultiBalance<B, AI> {
	fn checked_mul(&self, other: &Self) -> Option<Self> {
		<B>::checked_mul(&self.balance().clone(), &other.balance().clone())
			.map(|new_balance| self.update_balance(new_balance))
	}
}

impl<B: Div<Output = B>, AI> Div for MultiBalance<B, AI> {
	type Output = Self;
	fn div(self, other: Self) -> Self {
		self.update_balance(self.balance() / other.balance())
	}
}
impl<B: Div<Output = B>, AI> DivAssign for MultiBalance<B, AI> {
	fn div_assign(&mut self, other: Self) {
		*self = self.update_balance(self.balance() / other.balance())
	}
}
impl<B: CheckedDiv + Clone, AI> CheckedDiv for MultiBalance<B, AI> {
	fn checked_div(&self, other: &Self) -> Option<Self> {
		<B>::checked_div(&self.balance().clone(), &other.balance().clone())
			.map(|new_balance| self.update_balance(new_balance))
	}
}

impl<B: Rem<Output = B>, AI> Rem for MultiBalance<B, AI> {
	type Output = Self;
	fn rem(self, other: Self) -> Self {
		self.update_balance(self.balance() % other.balance())
	}
}
impl<B: Rem<Output = B>, AI> RemAssign for MultiBalance<B, AI> {
	fn rem_assign(&mut self, other: Self) {
		*self = self.update_balance(self.balance() % other.balance())
	}
}
impl<B: CheckedRem + Clone, AI> CheckedRem for MultiBalance<B, AI> {
	fn checked_rem(&self, other: &Self) -> Option<Self> {
		<B>::checked_rem(&self.balance().clone(), &other.balance().clone())
			.map(|new_balance| self.update_balance(new_balance))
	}
}
impl<B: IntegerSquareRoot + Clone, AI> IntegerSquareRoot for MultiBalance<B, AI> {
	fn integer_sqrt(&self) -> Self {
		self.update_balance(<B>::integer_sqrt(&self.balance().clone()))
	}
	fn integer_sqrt_checked(&self) -> Option<Self> {
		<B>::integer_sqrt_checked(&self.balance().clone())
			.map(|new_balance| self.update_balance(new_balance))
	}
}

impl<B: Zero, AI> Zero for MultiBalance<B, AI> {
	fn zero() -> Self {
		Self::Native(Zero::zero())
	}
	fn set_zero(&mut self) {
		match self {
			Self::Native(amount) => *amount = Zero::zero(),
			Self::Asset(_, amount) => *amount = Zero::zero(),
		}
	}
	fn is_zero(&self) -> bool {
		match self {
			Self::Native(amount) => amount.is_zero(),
			Self::Asset(_, amount) => amount.is_zero(),
		}
	}
}
impl<B: One + PartialEq, AI> One for MultiBalance<B, AI> {
	fn one() -> Self {
		Self::Native(One::one())
	}
	fn set_one(&mut self) {
		match self {
			Self::Native(amount) => *amount = One::one(),
			Self::Asset(_, amount) => *amount = One::one(),
		}
	}
	fn is_one(&self) -> bool {
		match self {
			Self::Native(amount) => amount.is_one(),
			Self::Asset(_, amount) => amount.is_one(),
		}
	}
}

impl<B: Bounded, AI> Bounded for MultiBalance<B, AI> {
	fn min_value() -> Self {
		Self::Native(<B>::min_value().into())
	}
	fn max_value() -> Self {
		Self::Native(<B>::max_value().into())
	}
}

use sp_std::marker::PhantomData;
pub struct MultiCurrencyAdapter<AccountId, Balance, Currency, Asset>(
	PhantomData<(AccountId, Balance, Currency, Asset)>,
);

impl<AccountId, Balance, Currency, Asset> MultiCurrency<AccountId>
	for MultiCurrencyAdapter<AccountId, Balance, Currency, Asset>
where
	Balance: BalanceTrait,
	// Currency: PalletCurrency<AccountId, Balance = Balance>,
	Currency: InspectFungible<AccountId, Balance = Balance> + TransferFungible<AccountId>,
	Asset: InspectFungibles<AccountId, AssetId = u32, Balance = Balance>
		+ TransferFungibles<AccountId>,
{
	type Balance = MultiBalance<Balance, u32>;

	fn transfer(
		source: &AccountId,
		dest: &AccountId,
		value: Self::Balance,
		existence_requirement: ExistenceRequirement,
	) -> DispatchResult {
		let keep_alive = existence_requirement == ExistenceRequirement::KeepAlive;
		match value {
			MultiBalance::Native(value) =>
				Currency::transfer(source, dest, value, keep_alive).map(|_| ()),
			MultiBalance::Asset(assetId, value) =>
				Asset::transfer(assetId, source, dest, value, keep_alive).map(|_| ()),
		}
	}
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type CollectionId = u32;
	type ItemId = u32;
	type Currency = Balances;
	type MultiCurrency =
		MultiCurrencyAdapter<u64, <Self as pallet_balances::Config>::Balance, Balances, Assets>;
	type CreateOrigin = AsEnsureOriginWithArg<frame_system::EnsureSigned<u64>>;
	type ForceOrigin = frame_system::EnsureRoot<u64>;
	type Locker = ();
	type CollectionDeposit = ConstU64<2>;
	type ItemDeposit = ConstU64<1>;
	type MetadataDepositBase = ConstU64<1>;
	type AttributeDepositBase = ConstU64<1>;
	type DepositPerByte = ConstU64<1>;
	type StringLimit = ConstU32<50>;
	type KeyLimit = ConstU32<50>;
	type ValueLimit = ConstU32<50>;
	type ApprovalsLimit = ConstU32<10>;
	type ItemAttributesApprovalsLimit = ConstU32<2>;
	type MaxTips = ConstU32<10>;
	type MaxDeadlineDuration = ConstU64<10000>;
	type Features = Features;
	type WeightInfo = ();
	type PalletId = NftsPalletId;
	#[cfg(feature = "runtime-benchmarks")]
	type Helper = ();
}

pub(crate) fn new_test_ext() -> sp_io::TestExternalities {
	let t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();

	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}
