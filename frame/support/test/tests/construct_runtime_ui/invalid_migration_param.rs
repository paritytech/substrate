use frame_support::{construct_runtime, derive_impl, traits::ConstU64};

type Block = frame_system::mocking::MockBlock<Runtime>;

#[derive_impl(frame_system::config_preludes::TestDefaultConfig as frame_system::DefaultConfig)]
impl frame_system::Config for Runtime {
	type Block = Block;
	type BlockHashCount = ConstU64<10>;
	type BaseCallFilter = frame_support::traits::Everything;
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type RuntimeEvent = RuntimeEvent;
	type PalletInfo = PalletInfo;
	type OnSetCode = ();
}

struct Dummy;

construct_runtime! {
	pub struct Runtime<Dummy>
	{
		System: frame_system
	}
}

fn main() {}
