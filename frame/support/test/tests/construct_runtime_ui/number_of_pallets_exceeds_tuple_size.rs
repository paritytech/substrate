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
	type Index = u64;
	type BlockNumber = u32;
	type RuntimeCall = RuntimeCall;
	type Hash = sp_runtime::testing::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Header = Header;
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
	pub struct Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_system,
		Pallet1: pallet,
		Pallet2: pallet,
		Pallet3: pallet,
		Pallet4: pallet,
		Pallet5: pallet,
		Pallet6: pallet,
		Pallet7: pallet,
		Pallet8: pallet,
		Pallet9: pallet,
		Pallet10: pallet,
		Pallet11: pallet,
		Pallet12: pallet,
		Pallet13: pallet,
		Pallet14: pallet,
		Pallet15: pallet,
		Pallet16: pallet,
		Pallet17: pallet,
		Pallet18: pallet,
		Pallet19: pallet,
		Pallet20: pallet,
		Pallet21: pallet,
		Pallet22: pallet,
		Pallet23: pallet,
		Pallet24: pallet,
		Pallet25: pallet,
		Pallet26: pallet,
		Pallet27: pallet,
		Pallet28: pallet,
		Pallet29: pallet,
		Pallet30: pallet,
		Pallet31: pallet,
		Pallet32: pallet,
		Pallet33: pallet,
		Pallet34: pallet,
		Pallet35: pallet,
		Pallet36: pallet,
		Pallet37: pallet,
		Pallet38: pallet,
		Pallet39: pallet,
		Pallet40: pallet,
		Pallet41: pallet,
		Pallet42: pallet,
		Pallet43: pallet,
		Pallet44: pallet,
		Pallet45: pallet,
		Pallet46: pallet,
		Pallet47: pallet,
		Pallet48: pallet,
		Pallet49: pallet,
		Pallet50: pallet,
		Pallet51: pallet,
		Pallet52: pallet,
		Pallet53: pallet,
		Pallet54: pallet,
		Pallet55: pallet,
		Pallet56: pallet,
		Pallet57: pallet,
		Pallet58: pallet,
		Pallet59: pallet,
		Pallet60: pallet,
		Pallet61: pallet,
		Pallet62: pallet,
		Pallet63: pallet,
		Pallet64: pallet,
		Pallet65: pallet,
		Pallet66: pallet,
		Pallet67: pallet,
		Pallet68: pallet,
		Pallet69: pallet,
		Pallet70: pallet,
		Pallet71: pallet,
		Pallet72: pallet,
		Pallet73: pallet,
		Pallet74: pallet,
		Pallet75: pallet,
		Pallet76: pallet,
		Pallet77: pallet,
		Pallet78: pallet,
		Pallet79: pallet,
		Pallet80: pallet,
		Pallet81: pallet,
		Pallet82: pallet,
		Pallet83: pallet,
		Pallet84: pallet,
		Pallet85: pallet,
		Pallet86: pallet,
		Pallet87: pallet,
		Pallet88: pallet,
		Pallet89: pallet,
		Pallet90: pallet,
		Pallet91: pallet,
		Pallet92: pallet,
		Pallet93: pallet,
		Pallet94: pallet,
		Pallet95: pallet,
		Pallet96: pallet,
		Pallet97: pallet,
		Pallet98: pallet,
		Pallet99: pallet,
		Pallet100: pallet,
		Pallet101: pallet,
		Pallet102: pallet,
		Pallet103: pallet,
		Pallet104: pallet,
		Pallet105: pallet,
		Pallet106: pallet,
		Pallet107: pallet,
		Pallet108: pallet,
		Pallet109: pallet,
		Pallet110: pallet,
	}
}

fn main() {}
