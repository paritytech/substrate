use frame_support::construct_runtime;
use sp_core::sr25519;
use sp_runtime::{generic, traits::BlakeTwo256};

#[frame_support::pallet]
mod pallet {
	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);
}

pub type Signature = sr25519::Signature;
pub type BlockNumber = u32;
pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<u32, RuntimeCall, Signature, ()>;

impl pallet::Config for Runtime {}

impl frame_system::Config for Runtime {
	type BaseCallFilter = frame_support::traits::Everything;
	type RuntimeOrigin = RuntimeOrigin;
	type Nonce = u64;
	type RuntimeCall = RuntimeCall;
	type Hash = sp_runtime::testing::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Block = Block;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = frame_support::traits::ConstU32<250>;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

construct_runtime! {
	pub struct Runtime
	{
		System: frame_system::{Pallet, Call, Storage, Config<T>, Event<T>},
		Pallet1: pallet::{Pallet},
		Pallet2: pallet::{Pallet},
		Pallet3: pallet::{Pallet},
		Pallet4: pallet::{Pallet},
		Pallet5: pallet::{Pallet},
		Pallet6: pallet::{Pallet},
		Pallet7: pallet::{Pallet},
		Pallet8: pallet::{Pallet},
		Pallet9: pallet::{Pallet},
		Pallet10: pallet::{Pallet},
		Pallet11: pallet::{Pallet},
		Pallet12: pallet::{Pallet},
		Pallet13: pallet::{Pallet},
		Pallet14: pallet::{Pallet},
		Pallet15: pallet::{Pallet},
		Pallet16: pallet::{Pallet},
		Pallet17: pallet::{Pallet},
		Pallet18: pallet::{Pallet},
		Pallet19: pallet::{Pallet},
		Pallet20: pallet::{Pallet},
		Pallet21: pallet::{Pallet},
		Pallet22: pallet::{Pallet},
		Pallet23: pallet::{Pallet},
		Pallet24: pallet::{Pallet},
		Pallet25: pallet::{Pallet},
		Pallet26: pallet::{Pallet},
		Pallet27: pallet::{Pallet},
		Pallet28: pallet::{Pallet},
		Pallet29: pallet::{Pallet},
		Pallet30: pallet::{Pallet},
		Pallet31: pallet::{Pallet},
		Pallet32: pallet::{Pallet},
		Pallet33: pallet::{Pallet},
		Pallet34: pallet::{Pallet},
		Pallet35: pallet::{Pallet},
		Pallet36: pallet::{Pallet},
		Pallet37: pallet::{Pallet},
		Pallet38: pallet::{Pallet},
		Pallet39: pallet::{Pallet},
		Pallet40: pallet::{Pallet},
		Pallet41: pallet::{Pallet},
		Pallet42: pallet::{Pallet},
		Pallet43: pallet::{Pallet},
		Pallet44: pallet::{Pallet},
		Pallet45: pallet::{Pallet},
		Pallet46: pallet::{Pallet},
		Pallet47: pallet::{Pallet},
		Pallet48: pallet::{Pallet},
		Pallet49: pallet::{Pallet},
		Pallet50: pallet::{Pallet},
		Pallet51: pallet::{Pallet},
		Pallet52: pallet::{Pallet},
		Pallet53: pallet::{Pallet},
		Pallet54: pallet::{Pallet},
		Pallet55: pallet::{Pallet},
		Pallet56: pallet::{Pallet},
		Pallet57: pallet::{Pallet},
		Pallet58: pallet::{Pallet},
		Pallet59: pallet::{Pallet},
		Pallet60: pallet::{Pallet},
		Pallet61: pallet::{Pallet},
		Pallet62: pallet::{Pallet},
		Pallet63: pallet::{Pallet},
		Pallet64: pallet::{Pallet},
		Pallet65: pallet::{Pallet},
		Pallet66: pallet::{Pallet},
		Pallet67: pallet::{Pallet},
		Pallet68: pallet::{Pallet},
		Pallet69: pallet::{Pallet},
		Pallet70: pallet::{Pallet},
		Pallet71: pallet::{Pallet},
		Pallet72: pallet::{Pallet},
		Pallet73: pallet::{Pallet},
		Pallet74: pallet::{Pallet},
		Pallet75: pallet::{Pallet},
		Pallet76: pallet::{Pallet},
		Pallet77: pallet::{Pallet},
		Pallet78: pallet::{Pallet},
		Pallet79: pallet::{Pallet},
		Pallet80: pallet::{Pallet},
		Pallet81: pallet::{Pallet},
		Pallet82: pallet::{Pallet},
		Pallet83: pallet::{Pallet},
		Pallet84: pallet::{Pallet},
		Pallet85: pallet::{Pallet},
		Pallet86: pallet::{Pallet},
		Pallet87: pallet::{Pallet},
		Pallet88: pallet::{Pallet},
		Pallet89: pallet::{Pallet},
		Pallet90: pallet::{Pallet},
		Pallet91: pallet::{Pallet},
		Pallet92: pallet::{Pallet},
		Pallet93: pallet::{Pallet},
		Pallet94: pallet::{Pallet},
		Pallet95: pallet::{Pallet},
		Pallet96: pallet::{Pallet},
		Pallet97: pallet::{Pallet},
		Pallet98: pallet::{Pallet},
		Pallet99: pallet::{Pallet},
		Pallet100: pallet::{Pallet},
		Pallet101: pallet::{Pallet},
		Pallet102: pallet::{Pallet},
		Pallet103: pallet::{Pallet},
		Pallet104: pallet::{Pallet},
		Pallet105: pallet::{Pallet},
		Pallet106: pallet::{Pallet},
		Pallet107: pallet::{Pallet},
		Pallet108: pallet::{Pallet},
		Pallet109: pallet::{Pallet},
		Pallet110: pallet::{Pallet},
	}
}

fn main() {}
