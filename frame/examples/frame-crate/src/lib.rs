use frame::prelude::*;

#[frame::pallet(dev_mode)]
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

	#[pallet::storage]
	pub type Value<T> = StorageValue<Value = u32>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		pub fn some_dispatchable(_origin: OriginFor<T>) -> DispatchResult {
			Ok(())
		}
	}
}

#[cfg(test)]
mod tests {
	use crate::pallet as my_pallet;
	use frame::{prelude::*, testing_prelude::*};

	construct_runtime!(
		pub struct Runtime {
			System: frame_system,
			MyPallet: my_pallet,
		}
	);

	#[derive_impl(frame_system::config_preludes::TestDefaultConfig as frame_system::DefaultConfig)]
	impl frame_system::Config for Runtime {
		type BaseCallFilter = frame::traits::Everything;
		type RuntimeOrigin = RuntimeOrigin;
		type RuntimeCall = RuntimeCall;
		type RuntimeEvent = RuntimeEvent;
		type PalletInfo = PalletInfo;
		type OnSetCode = ();
		type Block = MockBlock<Self>;
		type BlockHashCount = ();
	}

	impl my_pallet::Config for Runtime {
		type RuntimeEvent = RuntimeEvent;
	}
}
