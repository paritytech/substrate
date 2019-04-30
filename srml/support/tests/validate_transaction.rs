mod default_validate_transaction {
	use srml_system::{self as system};

	pub trait Trait: system::Trait {}

	srml_support::decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		}
	}
}

mod given_validate_transaction {
	use srml_system::{self as system};

	pub trait Trait: system::Trait {}

	srml_support::decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {
			fn transaction_validity(call: &Call<T>) -> Option<sr_primitives::transaction_validity::TransactionValidity> {
				None
			}
			fn validate_transaction(call: &Call<T>) -> Option<Result<(), ()>> {
				None
			}
		}
	}
}

mod wrong_transaction_validity_signature {
	/*!
	```compile_fail
		use srml_system::{self as system};

		pub trait Trait: system::Trait {}

		srml_support::decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin {
				fn transaction_validity() {}
			}
		}
	```
	*/
}

mod wrong_validate_transaction_signature {
	/*!
	```compile_fail
		use srml_system::{self as system};

		pub trait Trait: system::Trait {}

		srml_support::decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin {
				fn validate_transaction() {}
			}
		}
	```
	*/
}

mod missing_validate {
	/*!
	```compile_fail
		use srml_system::{self as system};

		pub trait Trait: system::Trait {}

		srml_support::decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin {
				fn validate_transaction(call: &Call<T>) -> Option<Result<(), ()>> {
					None
				}
			}
		}
	```
	*/
}

mod missing_validate_transaction {
	/*!
	```compile_fail
		use srml_system::{self as system};

		pub trait Trait: system::Trait {}

		srml_support::decl_module! {
			pub struct Module<T: Trait> for enum Call where origin: T::Origin {
				fn transaction_validity(call: &Call<T>) -> Option<sr_primitives::transaction_validity::TransactionValidity> {
					None
				}
			}
		}
	```
	*/
}
