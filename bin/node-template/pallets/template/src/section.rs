use frame_support::pallet_macros::*;

#[export_section]
mod section {

    // #[pallet::storage]
	// #[pallet::getter(fn something2)]
	// pub type Something2<T> = StorageValue<_, u32>;

	// Pallets use events to inform users when important changes are made.
	// https://docs.substrate.io/main-docs/build/events-errors/
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Event documentation should end with an array that provides descriptive names for event
		/// parameters. [something, who]
		SomethingStored { something: u32, who: T::AccountId },
	}


	pub fn t1() {}
}