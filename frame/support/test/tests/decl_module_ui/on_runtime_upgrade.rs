frame_support::decl_module! {
	pub struct Module<T: Config> for enum Call where origin: T::Origin, system=self {
		fn on_runtime_upgrade() -> Weight { 0 }
	}
}

fn main() {}
