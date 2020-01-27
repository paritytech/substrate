use super::*;

use frame_support::{
	impl_outer_origin, parameter_types, weights::Weight,
	ord_parameter_types, impl_outer_dispatch,
};
use sp_core::H256;
use frame_system::EnsureSignedBy;
// The testing primitives are very useful for avoiding having to work with signatures
// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
use sp_runtime::{
	Perbill, generic::Header, traits::{BlakeTwo256, IdentityLookup},
};

impl_outer_origin! {
	pub enum Origin for Benchmark  where system = frame_system {}
}

impl_outer_dispatch! {
	pub enum Call for Benchmark where origin: Origin {
		frame_system::System,
		pallet_balances::Balances,
		pallet_identity::Identity,
	}
}

// For testing the module, we construct most of a mock runtime. This means
// first constructing a configuration type (`Benchmark`) which `impl`s each of the
// configuration traits of modules we want to use.
#[derive(Clone, Eq, PartialEq)]
pub struct Benchmark;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
impl frame_system::Trait for Benchmark {
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Call = Call;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header<Self::BlockNumber, BlakeTwo256>;
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
}
parameter_types! {
	pub const ExistentialDeposit: u64 = 0;
	pub const TransferFee: u64 = 0;
	pub const CreationFee: u64 = 0;
}
impl pallet_balances::Trait for Benchmark {
	type Balance = u64;
	type OnFreeBalanceZero = ();
	type OnReapAccount = System;
	type OnNewAccount = ();
	type Event = ();
	type TransferPayment = ();
	type DustRemoval = ();
	type ExistentialDeposit = ExistentialDeposit;
	type TransferFee = TransferFee;
	type CreationFee = CreationFee;
}
parameter_types! {
	pub const BasicDeposit: u64 = 10;
	pub const FieldDeposit: u64 = 10;
	pub const SubAccountDeposit: u64 = 10;
	pub const MaximumSubAccounts: u32 = 2;
}
ord_parameter_types! {
	pub const One: u64 = 1;
	pub const Two: u64 = 2;
}
impl Trait for Benchmark {
	type Event = ();
	type Currency = Balances;
	type Slashed = ();
	type BasicDeposit = BasicDeposit;
	type FieldDeposit = FieldDeposit;
	type SubAccountDeposit = SubAccountDeposit;
	type MaximumSubAccounts = MaximumSubAccounts;
	type RegistrarOrigin = EnsureSignedBy<One, u64>;
	type ForceOrigin = EnsureSignedBy<Two, u64>;
}
type System = frame_system::Module<Benchmark>;
type Balances = pallet_balances::Module<Benchmark>;
type Identity = Module<Benchmark>;

pub type IdentityCall = crate::Call<Benchmark>;

pub mod set_identity {
	use super::*;

	pub fn components() -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// Registrar Count
			(BenchmarkParameter::R, 1, 16),
			// Additional Field Count
			(BenchmarkParameter::X, 1, 20)
		]
	}

	/// Assumes externalities are set up with a mutable state.
	///
	/// Panics if `component_name` isn't from `set_identity::components` or `component_value` is out of
	/// the range of `set_identity::components`.
	///
	/// Sets up state randomly and returns a randomly generated `set_identity` with sensible (fixed)
	/// values for all complexity components except those mentioned in the identity.
	pub fn instance(components: &[(BenchmarkParameter, u32)]) -> Call
	{
		// Add r registrars
		let r = components.iter().find(|&c| c.0 == BenchmarkParameter::R).unwrap();
		assert_eq!(Balances::set_balance(Origin::ROOT, 1u64.into(), 1_000_000_000_000, 0), Ok(()));
		for i in 0..r.1 {
			assert_eq!(Balances::set_balance(Origin::ROOT, i.into(), 1_000_000_000_000, 0), Ok(()));
			assert_eq!(Identity::add_registrar(Origin::signed(1), i.into()), Ok(()));
//			assert_eq!(Identity::set_fee(Origin::signed(i.into()), i, 10), Ok(()));
//			let fields = IdentityFields(IdentityField::Display | IdentityField::Legal);
//			assert_eq!(Identity::set_fields(Origin::signed(i.into()), 0, fields), Ok(()));
		}
		
		// Create identity info with x additional fields
		let x = components.iter().find(|&c| c.0 == BenchmarkParameter::X).unwrap();
		// 32 byte data that we reuse below
		let data = Data::Raw(vec![0; 32]);
		let info = IdentityInfo {
			additional: vec![(data.clone(), data.clone()); x.1 as usize],
			display: data.clone(),
			legal: data.clone(),
			web: data.clone(),
			riot: data.clone(),
			email: data.clone(),
			pgp_fingerprint: Some([0; 20]),
			image: data.clone(),
			twitter: data.clone(),
		};

		// Return the `set_identity` call
		return Call::Identity(IdentityCall::set_identity(info))
	}
}