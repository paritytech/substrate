
use super::*;

mod deprecated {
	use sp_std::prelude::*;

	use codec::{Encode, EncodeLike, Decode, Input, Output};
	use frame_support::{decl_module, decl_storage, Parameter};
	use sp_runtime::RuntimeDebug;
	use sp_std::convert::TryFrom;

	use crate::{Trait, BalanceOf, PropIndex, ReferendumIndex, Conviction, vote_threshold::VoteThreshold};

	#[derive(Copy, Clone, Eq, PartialEq, Default, RuntimeDebug)]
	pub struct Vote {
		pub aye: bool,
		pub conviction: Conviction,
	}

	impl Encode for Vote {
		fn encode_to<T: Output>(&self, output: &mut T) {
			output.push_byte(u8::from(self.conviction) | if self.aye { 0b1000_0000 } else { 0 });
		}
	}

	impl EncodeLike for Vote {}

	impl Decode for Vote {
		fn decode<I: Input>(input: &mut I) -> core::result::Result<Self, codec::Error> {
			let b = input.read_byte()?;
			Ok(Vote {
				aye: (b & 0b1000_0000) == 0b1000_0000,
				conviction: Conviction::try_from(b & 0b0111_1111)
					.map_err(|_| codec::Error::from("Invalid conviction"))?,
			})
		}
	}

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
	pub struct ReferendumInfo<BlockNumber: Parameter, Hash: Parameter> {
		/// When voting on this referendum will end.
		end: BlockNumber,
		/// The hash of the proposal being voted on.
		proposal_hash: Hash,
		/// The thresholding mechanism to determine whether it passed.
		threshold: VoteThreshold,
		/// The delay (in blocks) to wait after a successful referendum before deploying.
		delay: BlockNumber,
	}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin { }
	}
	decl_storage! {
		trait Store for Module<T: Trait> as Democracy {
			pub VotersFor get(fn voters_for):
				map hasher(opaque_blake2_256) ReferendumIndex => Vec<T::AccountId>;
			pub VoteOf get(fn vote_of):
				map hasher(opaque_blake2_256) (ReferendumIndex, T::AccountId) => Vote;
			pub Proxy get(fn proxy):
				map hasher(opaque_blake2_256) T::AccountId => Option<T::AccountId>;
			pub Delegations get(fn delegations):
				map hasher(opaque_blake2_256) T::AccountId => (T::AccountId, Conviction);
			
			// Note these actually used to be `blake2_256`, but this way we can migrate them
			// to then make use of them in the other migration.
			pub ReferendumInfoOf get(fn referendum_info):
				map hasher(twox_64_concat) ReferendumIndex
				=> Option<ReferendumInfo<T::BlockNumber, T::Hash>>;

			pub DepositOf get(fn deposit_of):
				map hasher(opaque_blake2_256) PropIndex => Option<(BalanceOf<T>, Vec<T::AccountId>)>;
			pub Preimages:
				map hasher(opaque_blake2_256) T::Hash
				=> Option<(Vec<u8>, T::AccountId, BalanceOf<T>, T::BlockNumber)>;
		}
	}
}

pub fn migrate_account<T: Trait>(a: &T::AccountId) {
	Locks::<T>::migrate_key_from_blake(a);
}

// The edgeware migration is so big we just assume it consumes the whole block.
pub fn migrate_all<T: Trait>() -> Weight {
	sp_runtime::print("🕊️  Migrating Democracy...");
	let mut weight = T::MaximumBlockWeight::get();
	sp_runtime::print("Democracy: Hasher");
	weight += migrate_hasher::<T>();
	sp_runtime::print("Democracy: Remove Unused");
	weight += migrate_remove_unused_storage::<T>();
	sp_runtime::print("Democracy: ReferendumInfo");
	weight += migrate_referendum_info::<T>();
	sp_runtime::print("🕊️  Done Democracy.");
	weight
}

pub fn migrate_hasher<T: Trait>() -> Weight {
	// Edgeware does not have any blacklist/cancellations that need to be migrated --> remove
	Blacklist::<T>::remove_all();
	Cancellations::<T>::remove_all();
	// Note this only migrates the hasher, `ReferendumInfoOf` is fully migrated in
	// `migrate_referendum_info`.
	sp_runtime::print("Democracy: Hasher: ReferendumInfo");
	for i in LowestUnbaked::get()..ReferendumCount::get() {
		deprecated::ReferendumInfoOf::<T>::migrate_key_from_blake(i);
	}
	sp_runtime::print("Democracy: Hasher: PublicProps");
	for (prop_idx, prop_hash, _) in PublicProps::<T>::get().into_iter() {
		// based on [democracy weights PR](https://github.com/paritytech/substrate/pull/5828/)
		if let Some((deposit, depositors)) = deprecated::DepositOf::<T>::take(prop_idx) {
			DepositOf::<T>::insert(prop_idx, (depositors, deposit));
		}
		// necessary because of [scheduler PR](https://github.com/paritytech/substrate/pull/5412)
		if let Some((data, provider, deposit, since)) = deprecated::Preimages::<T>::take(prop_hash) {
			Preimages::<T>::insert(prop_hash, PreimageStatus::Available{data, provider, deposit, since, expiry: None});
		}
	}
	0
}

pub fn migrate_remove_unused_storage<T: Trait>() -> Weight {
	// It's unlikely that Edgeware will have open proposals during the migration so we can assume
	// this to be fine.
	deprecated::VotersFor::<T>::remove_all();
	deprecated::VoteOf::<T>::remove_all();
	deprecated::Proxy::<T>::remove_all();
	deprecated::Delegations::<T>::remove_all();
	0
}

// migration based on [substrate/#5294](https://github.com/paritytech/substrate/pull/5294)
pub fn migrate_referendum_info<T: Trait>() -> Weight {
	use frame_support::{Twox64Concat, migration::{StorageKeyIterator}};
	
	let range = LowestUnbaked::get()..ReferendumCount::get();
	for (index, (end, proposal_hash, threshold, delay))
		in StorageKeyIterator::<
			ReferendumIndex,
			(T::BlockNumber, T::Hash, VoteThreshold, T::BlockNumber),
			Twox64Concat,
		>::new(b"Democracy", b"ReferendumInfoOf").drain()
	{
		if range.contains(&index) {
			let status = ReferendumStatus {
				end, proposal_hash, threshold, delay, tally: Tally::default()
			};
			ReferendumInfoOf::<T>::insert(index, ReferendumInfo::Ongoing(status))
		}
	}
	0
}