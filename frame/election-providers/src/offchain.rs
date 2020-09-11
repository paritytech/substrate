

use sp_std::marker::PhantomData;
use frame_support::{
	dispatch::{DispatchResult, IsSubType}, decl_module, decl_storage, decl_event,
	weights::{DispatchClass, ClassifyDispatch, WeighData, Weight, PaysFee, Pays},
};
use sp_std::prelude::*;
use frame_system::{ensure_signed, ensure_root};
use codec::{Encode, Decode};
use sp_runtime::{
	traits::{
		SignedExtension, Bounded, SaturatedConversion, DispatchInfoOf,
	},
	transaction_validity::{
		ValidTransaction, TransactionValidityError, InvalidTransaction, TransactionValidity,
	},
};

pub trait Trait: frame_system::Trait {}

decl_storage! {
	trait Store for Module<T: Trait> as OffchainElectionProvider {

	}
}

// decl_event!(
// 	pub enum Event<T> {
// 	}
// );

decl_module! {
	// Simple declaration of the `Module` type. Lets the macro know what its working on.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
}
