//! Runtime for testing an offchain worker.
//
// Inspired from pos-network-node/frame/contracts/src/tests.rs

use crate::{*, self as pallet_ddc_metrics_offchain_worker};

use codec::{Decode, Encode};
use frame_support::{
    impl_outer_dispatch, impl_outer_event, impl_outer_origin, parameter_types, traits::Get,
    weights::Weight,
};
use frame_support::traits::Currency;
use sp_core::H256;
use sp_runtime::{
    generic,
    testing::TestXt,
    traits::{
        BlakeTwo256, Convert, Extrinsic as ExtrinsicT, IdentifyAccount, IdentityLookup, Verify,
    },
    MultiSignature, Perbill,
};
use std::cell::RefCell;

pub type Signature = MultiSignature;
pub type AccountId = <<Signature as Verify>::Signer as IdentifyAccount>::AccountId;
pub type Balance = u128;
pub type BlockNumber = u32;
pub type Moment = u64;

// -- Implement a contracts runtime for testing --

// Macro hack: Give names to the pallets.
use frame_system as system;
use pallet_balances as balances;
use pallet_contracts as contracts;

mod example_offchain_worker {
    // Re-export contents of the root. This basically
    // needs to give a name for the current crate.
    // This hack is required for `impl_outer_event!`.
    pub use crate::*;
    pub use frame_support::impl_outer_event;
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
	    Contracts: contracts::{Pallet, Call, Config<T>, Storage, Event<T>},
        Timestamp: pallet_timestamp::{Pallet, Call, Storage, Inherent},
        Randomness: pallet_randomness_collective_flip::{Pallet, Call, Storage},
        DdcMetricsOffchainWorker: pallet_ddc_metrics_offchain_worker::{Pallet, Call, Event<T>},
    }
);

parameter_types! {
    pub const BlockHashCount: BlockNumber = 250;
    pub const MaximumBlockWeight: Weight = 1024;
    pub const MaximumBlockLength: u32 = 2 * 1024;
    pub const AvailableBlockRatio: Perbill = Perbill::one();
}

impl frame_system::Config for Test {
    type BaseCallFilter = ();
    type BlockWeights = ();
    type BlockLength = ();
    type Origin = Origin;
    type Index = u64;
    type BlockNumber = BlockNumber;
    type Hash = H256;
    type Call = Call;
    type Hashing = BlakeTwo256;
    type AccountId = AccountId;
    // u64; // sp_core::sr25519::Public;
    type Lookup = IdentityLookup<Self::AccountId>;
    type Header = generic::Header<BlockNumber, BlakeTwo256>;
    type Event = Event;
    type BlockHashCount = BlockHashCount;
    type DbWeight = ();
    type Version = ();
    type PalletInfo = PalletInfo;
    type AccountData = pallet_balances::AccountData<Balance>;
    type OnNewAccount = ();
    type OnKilledAccount = ();
    type SystemWeightInfo = ();
    type SS58Prefix = ();
    type OnSetCode = ();
}

impl pallet_balances::Config for Test {
    type Balance = Balance;
    type DustRemoval = ();
    type Event = Event;
    type ExistentialDeposit = ExistentialDeposit;
    type AccountStore = System;
    type WeightInfo = ();
    type MaxLocks = ();
}

thread_local! {
    static EXISTENTIAL_DEPOSIT: RefCell<Balance> = RefCell::new(1);
}

pub struct ExistentialDeposit;

impl Get<Balance> for ExistentialDeposit {
    fn get() -> Balance {
        EXISTENTIAL_DEPOSIT.with(|v| *v.borrow())
    }
}

parameter_types! {
    pub const MinimumPeriod: u64 = 1;
}
impl pallet_timestamp::Config for Test {
    type Moment = Moment;
    type OnTimestampSet = ();
    type MinimumPeriod = MinimumPeriod;
    type WeightInfo = ();
}
parameter_types! {
    pub const SignedClaimHandicap: BlockNumber = 2;
    pub const TombstoneDeposit: Balance = 16;
    pub const StorageSizeOffset: u32 = 8;
    pub const RentByteFee: Balance = 4;
    pub const RentDepositOffset: Balance = 10_000;
    pub const SurchargeReward: Balance = 150;
    pub const MaxDepth: u32 = 100;
    pub const MaxValueSize: u32 = 16_384;
    pub MaxCodeSize: u32 = 160 * 1024;
}

// Contracts for Test Runtime.
use contracts::{Config as contractsConfig};

type BalanceOf<T> = <<T as contractsConfig>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

impl contracts::Config for Test {
    type Time = Timestamp;
    type Randomness = Randomness;
    type Currency = Balances;
    type Event = Event;
    type RentPayment = ();
    type SignedClaimHandicap = SignedClaimHandicap;
    type TombstoneDeposit = TombstoneDeposit;
    type DepositPerContract = ();
    type DepositPerStorageByte = ();
    type DepositPerStorageItem = ();
    type RentFraction = ();
    type SurchargeReward = SurchargeReward;
    type CallStack = [pallet_contracts::Frame<Self>; 31];
    type MaxValueSize = MaxValueSize;
    type WeightPrice = Self; //pallet_transaction_payment::Module<Self>;
    type WeightInfo = ();
    type ChainExtension = ();
    type DeletionQueueDepth = ();
    type DeletionWeightLimit = ();
    type MaxCodeSize = MaxCodeSize;
}

parameter_types! {
    pub const TransactionByteFee: u64 = 0;
}

impl Convert<Weight, BalanceOf<Self>> for Test {
    fn convert(w: Weight) -> BalanceOf<Self> {
        w.into()
    }
}

// -- End contracts runtime --

use frame_system::offchain::{
    AppCrypto, CreateSignedTransaction, SendTransactionTypes, SigningTypes,
};

pub type Extrinsic = TestXt<Call, ()>;

impl SigningTypes for Test {
    type Public = <Signature as Verify>::Signer;
    type Signature = Signature;
}

impl<LocalCall> SendTransactionTypes<LocalCall> for Test
where
    Call: From<LocalCall>,
{
    type OverarchingCall = Call;
    type Extrinsic = Extrinsic;
}

impl<LocalCall> CreateSignedTransaction<LocalCall> for Test
where
    Call: From<LocalCall>,
{
    fn create_transaction<C: AppCrypto<Self::Public, Self::Signature>>(
        call: Call,
        _public: <Signature as Verify>::Signer,
        _account: AccountId,
        nonce: u64,
    ) -> Option<(Call, <Extrinsic as ExtrinsicT>::SignaturePayload)> {
        Some((call, (nonce, ())))
    }
}

parameter_types! {
    pub const OcwBlockInterval: u32 = crate::BLOCK_INTERVAL;
}

impl Config for Test {
    type BlockInterval = OcwBlockInterval;

    type AuthorityId = crypto::TestAuthId;

    type Event = Event;
    type Call = Call;
}
