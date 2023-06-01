/// The kitchen-sink catalog of the the FRAME macros and their various syntax options.
///
/// This example does not focus on pallet instancing, `dev_mode`, and does nto include any 'where'
/// clauses on `T`. These will both incur additional complexity to the syntax, but are not discussed
/// here.
// TODO: link to a particular example pallet that highlights each of these.
// https://github.com/paritytech/substrate/issues/13951

// Re-export pallet items so that they can be accessed from the crate namespace.
pub use pallet::*;

#[cfg(test)]
mod tests;

mod benchmarking;

#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	/// The config trait of the pallet. You can basically do anything with the config trait that you
	/// can do with a normal rust trait: import items consisting of types, constants and functions.
	///
	/// A very common pattern is for a pallet to import implementations of traits such as
	/// [`frame_support::traits::Currency`], [`frame_support::traits::fungibles::Inspect`] and
	/// [`frame_support::traits::Get`]. These are all types that the pallet is delegating to the top
	/// level runtime to provide to it.
	///
	/// The `FRAME`-specific syntax are:
	///
	/// * the use of `#[pallet::constant]`([`frame_support::procedural`]), which places a `Get`
	///   implementation in the metadata.
	/// * `type RuntimeEvent`, which is mandatory if your pallet has events. See TODO.
	/// * Needless to say, because [`Config`] is bounded by [`frame_system::Config`], you can use
	///   all the items from [`frame_system::Config`] as well, such as `AccountId`.
	/// * `#[pallet::disable_frame_system_supertrait_check]` would remove the need for
	///   `frame_system::Config` to exist, which you should almost never need.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching runtime event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// This is a normal Rust type, nothing specific to FRAME here.
		type Currency: frame_support::traits::tokens::fungible::Inspect<Self::AccountId>;

		/// Similarly, let the runtime decide this.
		fn some_function() -> u32;

		/// And this
		const FOO: u32;

		/// This is a FRAME-specific item. It will be placed in the metadata of the pallet, and
		/// therefore can be queried by offchain applications.
		#[pallet::constant]
		type InMetadata: Get<u32>;
	}

	#[pallet::extra_constants]
	impl<T: Config> Pallet<T> {
		#[allow(non_snake_case)]
		fn SomeValue() -> u32 {
			unimplemented!()
		}

		#[pallet::constant_name(OtherValue)]
		fn arbitrary_name() -> u32 {
			unimplemented!()
		}
	}

	const STORAGE_VERSION: frame_support::traits::StorageVersion = StorageVersion::new(1);

	/// The pallet struct. There's nothing special to FRAME about this; it can implement functions
	/// in an impl blocks, traits and so on.
	#[pallet::pallet]
	// #[pallet::generate_storage_info] // TODO: should be removed.
	#[pallet::without_storage_info]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::origin]
	pub type Origin<T> = frame_system::RawOrigin<<T as frame_system::Config>::AccountId>;

	// first, we showcase all the possible storage types, with most of their details.

	/// A storage value. We mark this as unbounded, alter its prefix, and define a custom storage
	/// getter for it.
	///
	/// The value is stored a single trie node, and therefore can be retrieved with a single
	/// database access.
	#[pallet::storage]
	#[pallet::unbounded] // optional
	#[pallet::storage_prefix = "OtherFoo"] // optional
	#[pallet::getter(fn foo)] // optional
	pub type Foo<T> = StorageValue<Value = u32>;

	#[pallet::type_value]
	pub fn DefaultForFoo() -> u32 {
		1
	}

	#[pallet::storage]
	pub type FooWithDefault<T> =
		StorageValue<Value = u32, QueryKind = ValueQuery, OnEmpty = DefaultForFoo>;

	/// A storage map. This creates a mapping from keys of type `u32` to values of type `u32`.
	///
	/// Keys and values can be iterated, albeit each value is stored under a unique trie key,
	/// meaning that an iteration consists of many database accesses.
	#[pallet::storage]
	pub type Bar<T> = StorageMap<Hasher = Blake2_128Concat, Key = u32, Value = u32>;

	/// Conceptually same as `StorageMap<>` where the key is a tuple of `(u32, u32)`. On top, it
	/// provides some functions to iterate or remove items based on only the first key.
	#[pallet::storage]
	pub type Qux<T> = StorageDoubleMap<
		Hasher1 = Blake2_128Concat,
		Key1 = u32,
		Hasher2 = Blake2_128Concat,
		Key2 = u32,
		Value = u32,
	>;

	/// Same as `StorageDoubleMap`, but with arbitrary number of keys.
	#[pallet::storage]
	pub type Quux<T> = StorageNMap<
		Key = (
			NMapKey<Blake2_128Concat, u8>,
			NMapKey<Blake2_128Concat, u16>,
			NMapKey<Blake2_128Concat, u32>,
		),
		Value = u64,
	>;

	/// In all of these examples, we chose a syntax where the storage item is defined using the
	/// explicit generic syntax (`X = Y`). Alternatively:
	#[pallet::storage]
	pub type AlternativeSyntax<T> = StorageMap<_, Blake2_128Concat, u32, u32>;

	/// Lastly, all storage items, as you saw, had to be generic over `T`. If they want to use an
	/// item from `Config`, `<T: Config>` should be used.
	#[pallet::storage]
	pub type AlternativeSyntax2<T: Config> = StorageMap<_, Blake2_128Concat, T::AccountId, u32>;

	/// The genesis config type. This allows the pallet to define how it should initialized upon
	/// genesis.
	///
	/// It can be generic over `T` or not, depending on whether it is or not.
	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub foo: u32,
		pub bar: T::BlockNumber,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			unimplemented!()
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::call_index(0)]
		#[pallet::weight(0)]
		pub fn set_foo(
			_: OriginFor<T>,
			new_foo: u32,
			#[pallet::compact] _other_compact: u128,
		) -> DispatchResult {
			Foo::<T>::set(Some(new_foo));

			Ok(())
		}
	}

	/// The event type. This exactly like a normal Rust enum.
	///
	/// It can or cannot be generic over `<T: Config>`. Note that unlike a normal enum, if none of
	/// the variants actually use `<T: Config>`, the macro will generate a hidden `PhantomData`
	/// variant.
	///
	/// The `generate_deposit` macro generates a function on `Pallet` called `deposit_event` which
	/// will properly convert the error type of your pallet into `RuntimeEvent` (recall `type
	/// RuntimeEvent: From<Event<Self>>`, so it can be converted) and deposit it via
	/// `frame_system::Pallet::deposit_event`.
	#[pallet::event]
	#[pallet::generate_deposit(pub fn deposit_event)]
	pub enum Event<T: Config> {
		/// A simple tuple style variant.
		SomethingHappened(u32),
		/// A simple struct-style variant. Note that we use `AccountId` from `T` because `T:
		/// Config`, which by extension implies `T: frame_system::Config`.
		SomethingDetailedHappened {
			at: u32,
			to: T::AccountId,
		},
		// /// Another variant.
		SomeoneJoined(T::AccountId),
	}

	/// The error enum. Must always be generic over `<T>`, which is expanded to `<T: Config>`.
	#[pallet::error]
	pub enum Error<T> {
		SomethingWentWrong,
		SomethingBroke,
	}

	/// All the possible hooks that a pallet can have. See [`frame_support::traits::Hooks`] for more
	/// info.
	#[pallet::hooks]
	impl<T: Config> Hooks<T::BlockNumber> for Pallet<T> {
		fn integrity_test() {
			
		}

		fn offchain_worker(_n: T::BlockNumber) {
			unimplemented!()
		}

		fn on_initialize(_n: T::BlockNumber) -> Weight {
			unimplemented!()
		}

		fn on_finalize(_n: T::BlockNumber) {
			unimplemented!()
		}

		fn on_idle(_n: T::BlockNumber, _remaining_weight: Weight) -> Weight {
			unimplemented!()
		}

		fn on_runtime_upgrade() -> Weight {
			unimplemented!()
		}

		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<Vec<u8>, TryRuntimeError> {
			unimplemented!()
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade(_state: Vec<u8>) -> Result<(), TryRuntimeError> {
			unimplemented!()
		}

		#[cfg(feature = "try-runtime")]
		fn try_state(_n: T::BlockNumber) -> Result<(), TryRuntimeError> {
			unimplemented!()
		}
	}

	#[pallet::composite_enum]
	pub enum HoldReason {
		Staking,
	}

	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T> {
		type Call = Call<T>;
		fn validate_unsigned(_: TransactionSource, _: &Self::Call) -> TransactionValidity {
			unimplemented!()
		}

		fn pre_dispatch(_: &Self::Call) -> Result<(), TransactionValidityError> {
			unimplemented!()
		}
	}

	#[pallet::inherent]
	impl<T: Config> ProvideInherent for Pallet<T> {
		type Call = Call<T>;
		type Error = MakeFatalError<()>;

		const INHERENT_IDENTIFIER: [u8; 8] = *b"test1234";

		fn create_inherent(_data: &InherentData) -> Option<Self::Call> {
			unimplemented!();
		}

		fn is_inherent(_call: &Self::Call) -> bool {
			unimplemented!()
		}
	}
}
