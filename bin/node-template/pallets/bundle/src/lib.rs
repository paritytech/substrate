#![cfg_attr(not(feature = "std"), no_std)]

/// Edit this file to define custom logic or remove it if it is not needed.
/// Learn more about FRAME and the core library of Substrate FRAME pallets:
/// <https://docs.substrate.io/reference/frame-pallets/>
pub use pallet::*;

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
pub mod weights;
pub use weights::*;

pub use frame_support::construct_bundle;

#[frame_support::pallet(bundle)]
pub mod pallet {
	use super::*;
	use frame_support::{pallet_prelude::*, Parameter, dispatch::GetDispatchInfo};
	use frame_system::pallet_prelude::*;
	use frame_support::dispatch::CallableCallFor;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	/// Configure the pallet by specifying the parameters and types on which it depends.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Because this pallet emits events, it depends on the runtime's definition of an event.
		type RuntimeEvent: Parameter + Sync + Send + From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
			// + From<pallet_template::Event<Bundle<Self>>> + From<pallet_template_2::Event<Bundle<Self>>>
			// + From<frame_system::Event<Bundle<Self>>>;
		/// Type representing the weight of this pallet
		type WeightInfo: WeightInfo;

		// /// A dispatchable call.
		// type RuntimeCall: Parameter
		// 	+ Dispatchable<RuntimeOrigin = Self::RuntimeOrigin>
		// 	+ GetDispatchInfo
		// 	+ From<frame_system::Call<Self>>;
	}

	// The pallet's runtime storage items.
	// https://docs.substrate.io/main-docs/build/runtime-storage/
	#[pallet::storage]
	#[pallet::getter(fn something3)]
	// Learn more about declaring storage items:
	// https://docs.substrate.io/main-docs/build/runtime-storage/#declaring-storage-items
	pub type Something3<T> = StorageValue<_, u32>;

	// Pallets use events to inform users when important changes are made.
	// https://docs.substrate.io/main-docs/build/events-errors/
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Event documentation should end with an array that provides descriptive names for event
		/// parameters. [something, who]
		SomethingStored { something: u32, who: T::AccountId },
	}

	// Errors inform users that something went wrong.
	#[pallet::error]
	pub enum Error<T> {
		/// Error names should be descriptive.
		NoneValue,
		/// Errors should have helpful documentation associated with them.
		StorageOverflow,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
	}

	construct_bundle!(
		pub struct Bundle {
			Template: pallet_template,
			Template2: pallet_template_2
		}
	);

	impl<T: Config> frame_system::Config for Bundle<T> {
		type BaseCallFilter = <T as frame_system::Config>::BaseCallFilter;
		type BlockWeights = <T as frame_system::Config>::BlockWeights;
		type BlockLength = <T as frame_system::Config>::BlockLength;
		type DbWeight = <T as frame_system::Config>::DbWeight;
		type RuntimeOrigin = <T as frame_system::Config>::RuntimeOrigin;
		type RuntimeCall = <T as frame_system::Config>::RuntimeCall;
		type Index = <T as frame_system::Config>::Index;
		type BlockNumber = <T as frame_system::Config>::BlockNumber;
		type Hash = <T as frame_system::Config>::Hash;
		type Hashing = <T as frame_system::Config>::Hashing;
		type AccountId = <T as frame_system::Config>::AccountId;
		type Lookup = <T as frame_system::Config>::Lookup;
		type Header = <T as frame_system::Config>::Header;
		type RuntimeEvent = <T as Config>::RuntimeEvent;
		type BlockHashCount = <T as frame_system::Config>::BlockHashCount;
		type Version = <T as frame_system::Config>::Version;
		type PalletInfo = <T as frame_system::Config>::PalletInfo;
		type AccountData = <T as frame_system::Config>::AccountData;
		type OnNewAccount = <T as frame_system::Config>::OnNewAccount;
		type OnKilledAccount = <T as frame_system::Config>::OnKilledAccount;
		type SystemWeightInfo = <T as frame_system::Config>::SystemWeightInfo;
		type SS58Prefix = <T as frame_system::Config>::SS58Prefix;
		type OnSetCode = ();
		type MaxConsumers = <T as frame_system::Config>::MaxConsumers;
	}

	impl<T: Config> pallet_template::Config for Bundle<T> {
		type RuntimeEvent = <T as pallet::Config>::RuntimeEvent;
		type WeightInfo = pallet_template::weights::SubstrateWeight<T>;
	}

	impl<T: Config> pallet_template_2::Config for Bundle<T> {
		type RuntimeEvent = <T as pallet::Config>::RuntimeEvent;
		type WeightInfo = pallet_template_2::weights::SubstrateWeight<T>;
	}
}