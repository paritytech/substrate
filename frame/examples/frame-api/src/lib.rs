use frame::prelude::*;

#[frame::pallet]
pub mod pallet {
	use super::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type RuntimeEvent: IsType<<Self as frame_system::Config>::RuntimeEvent> + From<Event<Self>>;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);

	#[pallet::event]
	pub enum Event<T: Config> {}
}

#[cfg(test)]
mod tests {
	use super::pallet as pallet_example;
	use frame::{prelude::*, testing_prelude::*};

	/// To use the derive-impl, this line must be provided as-is.
	#[frame::macros::use_attr]
	use frame::deps::frame_support::derive_impl;

	type UncheckedExtrinsic = MockUncheckedExtrinsic<Test>;
	type Block = MockBlock<Test>;

	For testing the pallet, we construct a mock runtime.
	construct_runtime!(
		pub enum Test
		where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
			{
				System: frame_system,
				Example: pallet_example,
			}
	);

	#[derive_impl(frame_system::config_preludes::TestDefaultConfig as frame_system::DefaultConfig)]
	impl frame_system::Config for Test {
		// these items are defined by frame-system as `no_default`, so we must specify them here.
		// Note that these are types that actually rely on the outer runtime, and can't sensibly
		// have an _independent_ default.
		type BaseCallFilter = frame_support::traits::Everything;
		type RuntimeOrigin = RuntimeOrigin;
		type RuntimeCall = RuntimeCall;
		type RuntimeEvent = RuntimeEvent;
		type PalletInfo = PalletInfo;
		type OnSetCode = ();
	}

	impl pallet_example::Config for Test {
		type RuntimeEvent = RuntimeEvent;
	}
}
