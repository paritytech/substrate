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
use frame_support::traits::Contains;
use frame_support::traits::OriginTrait;
use frame_support::dispatch::RawOrigin;
use frame_support::dispatch::Dispatchable;

#[frame_support::pallet(bundle)]
pub mod pallet {
	use super::*;
	use frame_support::{pallet_prelude::*, Parameter, dispatch::GetDispatchInfo};
	use frame_system::pallet_prelude::*;
	use frame_support::dispatch::CallableCallFor;
	use frame_support::dispatch::fmt::Debug;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	/// Configure the pallet by specifying the parameters and types on which it depends.
	#[pallet::config]
	pub trait Config: frame_system::Config + TypeInfo + Sync + Send + Debug {
		// /// Because this pallet emits events, it depends on the runtime's definition of an event.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
			// + From<pallet_template::Event<Bundle<Self>>> + From<pallet_template_2::Event<Bundle<Self>>>
			// + From<frame_system::Event<Self>>;
		/// Type representing the weight of this pallet
		type WeightInfo: WeightInfo;

		// // /// A dispatchable call.
		// type RuntimeCall: Parameter
		// 	+ Dispatchable<RuntimeOrigin = Origin<Self>> // <Self as Config>::RuntimeOrigin>
		// 	+ GetDispatchInfo
		// 	+ From<Call<Self>>;

		// type BaseCallFilter: Contains<Call<Self>>;

		// type RuntimeOrigin: Into<Result<RawOrigin<Self::AccountId>, <Self as Config>::RuntimeOrigin>>
		// 	+ From<RawOrigin<Self::AccountId>>
		// 	+ Clone
		// 	+ OriginTrait<Call = <Self as Config>::RuntimeCall, AccountId = Self::AccountId>;
	}

	// The pallet's runtime storage items.
	// https://docs.substrate.io/main-docs/build/runtime-storage/
	#[pallet::storage]
	#[pallet::getter(fn something3)]
	// Learn more about declaring storage items:
	// https://docs.substrate.io/main-docs/build/runtime-storage/#declaring-storage-items
	pub type Something3<T> = StorageValue<_, u32>;

	// // Pallets use events to inform users when important changes are made.
	// // https://docs.substrate.io/main-docs/build/events-errors/
	// #[pallet::event]
	// #[pallet::generate_deposit(pub(super) fn deposit_event)]
	// pub enum Event<T: Config> {
	// 	/// Event documentation should end with an array that provides descriptive names for event
	// 	/// parameters. [something, who]
	// 	SomethingStored { something: u32, who: T::AccountId },
	// }

	// Errors inform users that something went wrong.
	#[pallet::error]
	pub enum Error<T> {
		/// Error names should be descriptive.
		NoneValue,
		/// Errors should have helpful documentation associated with them.
		StorageOverflow,
	}

	// #[derive(
	// 	Clone, PartialEq, Eq,
	// 	frame_support::codec::Encode,
	// 	frame_support::codec::Decode,
	// 	frame_support::scale_info::TypeInfo,
	// 	frame_support::RuntimeDebug,
	// )]
	#[pallet::event]
	// #[derive(
	// 	frame_support::CloneNoBound,
	// 	frame_support::EqNoBound,
	// 	frame_support::PartialEqNoBound,
	// 	frame_support::RuntimeDebugNoBound,
	// 	frame_support::codec::Encode,
	// 	frame_support::codec::Decode,
	// 	frame_support::scale_info::TypeInfo,
	// )]
	#[allow(non_camel_case_types)]
	pub enum Event<T: Config> {
		// #[doc(hidden)]
		// #[codec(skip)]
		// __Ignore(
		// 	frame_support::sp_std::marker::PhantomData<T>,
		// 	frame_support::Never,
		// ),
		// #[codec(index = 0u8)]
    	// System(frame_system::Event<Pallet<T>>),
		#[codec(index = 0u8)]
    	Template(pallet_template::Event<Pallet<T>>),
		#[codec(index = 1u8)]
    	Template_2(pallet_template_2::Event<Pallet<T>>),
	}

	// impl<T: Config> From<frame_system::Event<Pallet<T>>> for Event<T> {
	// 	fn from(x: frame_system::Event<Pallet<T>>) -> Self {
	// 		Self::System(x)
	// 	}
	// }
	
	// impl<T: Config> TryInto<frame_system::Event<Pallet<T>>> for Event<T> {
	// 	type Error = ();

	// 	fn try_into(self) -> frame_support::sp_std::result::Result<frame_system::Event<Pallet<T>>, Self::Error> {
	// 		match self {
	// 			Self::System(evt) => Ok(evt),
	// 			_ => Err(()),
	// 		}
	// 	}
	// }

	impl<T: Config> From<pallet_template::Event<Pallet<T>>> for Event<T> {
		fn from(x: pallet_template::Event<Pallet<T>>) -> Self {
			Self::Template(x)
		}
	}
	
	impl<T: Config> TryInto<pallet_template::Event<Pallet<T>>> for Event<T> {
		type Error = ();

		fn try_into(self) -> frame_support::sp_std::result::Result<pallet_template::Event<Pallet<T>>, Self::Error> {
			match self {
				Self::Template(evt) => Ok(evt),
				_ => Err(()),
			}
		}
	}

	impl<T: Config> From<pallet_template_2::Event<Pallet<T>>> for Event<T> {
		fn from(x: pallet_template_2::Event<Pallet<T>>) -> Self {
			Self::Template_2(x)
		}
	}
	
	impl<T: Config> TryInto<pallet_template_2::Event<Pallet<T>>> for Event<T> {
		type Error = ();

		fn try_into(self) -> frame_support::sp_std::result::Result<pallet_template_2::Event<Pallet<T>>, Self::Error> {
			match self {
				Self::Template_2(evt) => Ok(evt),
				_ => Err(()),
			}
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
	}

	construct_bundle!(
		pub struct Bundle {
			System: frame_system,
			Template: pallet_template,
			Template2: pallet_template_2
		}
	);

	impl<T: Config> frame_system::Config for Pallet<T> {
		type BaseCallFilter = frame_support::traits::Everything;//<T as Config>::BaseCallFilter;
		type BlockWeights = <T as frame_system::Config>::BlockWeights;
		type BlockLength = <T as frame_system::Config>::BlockLength;
		type DbWeight = <T as frame_system::Config>::DbWeight;
		type RuntimeOrigin = <T as frame_system::Config>::RuntimeOrigin;
		type RuntimeCall = <T as frame_system::Config>::RuntimeCall;
		type Nonce = <T as frame_system::Config>::Nonce;
		type Block = <T as frame_system::Config>::Block;
		type Hash = <T as frame_system::Config>::Hash;
		type Hashing = <T as frame_system::Config>::Hashing;
		type AccountId = <T as frame_system::Config>::AccountId;
		type Lookup = <T as frame_system::Config>::Lookup;
		type RuntimeEvent = <T as frame_system::Config>::RuntimeEvent;
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

	impl<T: Config> pallet_template::Config for Pallet<T> {
		type RuntimeEvent = <T as frame_system::Config>::RuntimeEvent;//Event<T>;
		type WeightInfo = pallet_template::weights::SubstrateWeight<T>;
	}

	impl<T: Config> pallet_template_2::Config for Pallet<T> {
		type RuntimeEvent = <T as frame_system::Config>::RuntimeEvent;//Event<T>;
		type WeightInfo = pallet_template_2::weights::SubstrateWeight<T>;
	}

	// impl<T: Config> Config for Pallet<T> {
	// 	type RuntimeEvent = Event<T>;
	// 	type WeightInfo = weights::SubstrateWeight<T>;
	// }
}