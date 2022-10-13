use frame_support::construct_runtime;

mod pallet_old {
	pub trait Config: frame_system::Config {}

	decl_storage! {
		trait Store for Module<T: Config> as Example {}
	}

	decl_module! {
		pub struct Module<T: Config> for enum Call where origin: T::Origin {}
	}

}
construct_runtime! {
	pub enum Runtime where
		UncheckedExtrinsic = UncheckedExtrinsic,
		Block = Block,
		NodeBlock = Block,
	{
		System: frame_system,
		OldPallet: pallet_old,
	}
}

fn main() {}
