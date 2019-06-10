#![cfg(test)]

use super::*;
use runtime_io::with_externalities;
use srml_support::{decl_module, impl_outer_origin, dispatch::Result};
use system::{self, ensure_signed};
use substrate_primitives::{Blake2Hasher, H256};
use primitives::{
	BuildStorage,
	traits::{BlakeTwo256, IdentityLookup},
	testing::{Digest, DigestItem, Header}
};

impl_outer_origin! {
	pub enum Origin for Test {}
}

type Balance = balances::Module<Test>;

#[derive(Clone, Eq, PartialEq)]
pub struct Test;

impl system::Trait for Test {
	type Origin = Origin;
	type Index = u32;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type Digest = Digest;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
	type Log = DigestItem;
}

impl balances::Trait for Test {
	type Balance = u64;
	type OnFreeBalanceZero = ();
	type OnNewAccount = ();
	type Event = ();
	type TransactionPayment = ();
	type TransferPayment = ();
	type DustRemoval = ();
}

impl OnSlashing for Test {
	type Currency = Balance;
	type Misconduct = Unresponsive;
	type Slashing = Self;

	fn slash(
		who: &Self::AccountId,
		free_balance: BalanceOf<Self>,
		misconduct: &mut Self::Misconduct
	) -> (NegativeImbalanceOf<Self>, BalanceOf<Self>) {
		let slashed_amount = Self::Slashing::amount(free_balance, misconduct.severity());
		let (imbalance, remaining) = Self::Currency::slash(&who, slashed_amount);
		misconduct.on_misconduct();
		(imbalance, remaining)
	}

	fn on_signal(misconduct: &mut Self::Misconduct) {
		misconduct.on_signal();
	}
}

impl Slashing for Test {
	fn amount(free_balance: BalanceOf<Self>, severity: Severity<Self>) -> BalanceOf<Self> {
		free_balance / severity
	}
}

decl_module! {
	pub struct Module<T: OnSlashing> for enum Call where origin: T::Origin {
		pub fn system_module_example(origin) -> Result {
			let _sender = ensure_signed(origin)?;
			let _random_seed = <system::Module<T>>::random_seed();
			let _extrinsic_count = <system::Module<T>>::extrinsic_count();
			Ok(())
		}
	}
}

#[derive(Default)]
pub struct ExtBuilder;

impl ExtBuilder {
	pub fn build(self) -> runtime_io::TestExternalities<Blake2Hasher> {
		system::GenesisConfig::<Test>::default().build_storage().unwrap().0.into()
	}
}

#[test]
fn unresponsive_basic() {
	let mut m = Unresponsive::default();
	assert_eq!(m.severity(), 100_000);

	m.on_misconduct();
	assert_eq!(m.severity(), 50_000);

	m.on_misconduct();
	assert_eq!(m.severity(), 25_000);

	m.on_misconduct();
	assert_eq!(m.severity(), 12_500);

	m.on_misconduct();
	assert_eq!(m.severity(), 6_250);

	m.on_misconduct();
	assert_eq!(m.severity(), 3_125);

	m.on_misconduct();
	assert_eq!(m.severity(), 1_562);

	m.on_signal();
	assert_eq!(m.severity(), 3_124);
}


#[test]
fn unresponsive_should_handle_overflow() {
	let mut m = Unresponsive::default();
	assert_eq!(m.severity(), 100_000);

	m.on_signal();
	assert_eq!(m.severity(), 100_000);

	while m.severity() > 1 {
		m.on_misconduct();
	}

	m.on_misconduct();
	assert_eq!(m.severity(), 1);
}


#[test]
fn it_works() {
	// Verifies initial conditions of mock
	with_externalities(&mut ExtBuilder::default()
		.build(),
	|| {
		let who = 0;
		let mut misconduct = Unresponsive::default();

		let _ = Balance::deposit_creating(&who, 100_000);
		assert_eq!(Balance::free_balance(&0), 100_000);


		let (_imba, _rem) = Test::slash(&who, Balance::free_balance(&0), &mut misconduct);
		assert_eq!(Balance::free_balance(&0), 99_999);

		let (_imba, _rem) = Test::slash(&who, Balance::free_balance(&0), &mut misconduct);
		assert_eq!(Balance::free_balance(&0), 99_998);

		let (_imba, _rem) = Test::slash(&who, Balance::free_balance(&0), &mut misconduct);
		assert_eq!(Balance::free_balance(&0), 99_995);
	});
}
