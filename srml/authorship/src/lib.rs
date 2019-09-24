// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Authorship tracking for SRML runtimes.
//!
//! This tracks the current author of the block and recent uncles.

#![cfg_attr(not(feature = "std"), no_std)]

use rstd::{result, prelude::*};
use rstd::collections::btree_set::BTreeSet;
use support::{decl_module, decl_storage};
use support::traits::{FindAuthor, VerifySeal, Get};
use support::dispatch::Result as DispatchResult;
use codec::{Encode, Decode};
use system::ensure_none;
use sr_primitives::traits::{Header as HeaderT, One, Zero};
use sr_primitives::weights::SimpleDispatchInfo;
use inherents::{
	RuntimeString, InherentIdentifier, ProvideInherent,
	InherentData, MakeFatalError,
};

/// The identifier for the `uncles` inherent.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"uncles00";

/// Auxiliary trait to extract uncles inherent data.
pub trait UnclesInherentData<H: Decode> {
	/// Get uncles.
	fn uncles(&self) -> Result<Vec<H>, RuntimeString>;
}

impl<H: Decode> UnclesInherentData<H> for InherentData {
	fn uncles(&self) -> Result<Vec<H>, RuntimeString> {
		Ok(self.get_data(&INHERENT_IDENTIFIER)?.unwrap_or_default())
	}
}

/// Provider for inherent data.
#[cfg(feature = "std")]
pub struct InherentDataProvider<F, H> {
	inner: F,
	_marker: std::marker::PhantomData<H>,
}

#[cfg(feature = "std")]
impl<F, H> InherentDataProvider<F, H> {
	pub fn new(uncles_oracle: F) -> Self {
		InherentDataProvider { inner: uncles_oracle, _marker: Default::default() }
	}
}

#[cfg(feature = "std")]
impl<F, H: Encode + std::fmt::Debug> inherents::ProvideInherentData for InherentDataProvider<F, H>
where F: Fn() -> Vec<H>
{
	fn inherent_identifier(&self) -> &'static InherentIdentifier {
		&INHERENT_IDENTIFIER
	}

	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), RuntimeString> {
		let uncles = (self.inner)();
		if !uncles.is_empty() {
			inherent_data.put_data(INHERENT_IDENTIFIER, &uncles)
		} else {
			Ok(())
		}
	}

	fn error_to_string(&self, _error: &[u8]) -> Option<String> {
		Some(format!("no further information"))
	}
}

pub trait Trait: system::Trait {
	/// Find the author of a block.
	type FindAuthor: FindAuthor<Self::AccountId>;
	/// The number of blocks back we should accept uncles.
	/// This means that we will deal with uncle-parents that are
	/// `UncleGenerations + 1` before `now`.
	type UncleGenerations: Get<Self::BlockNumber>;
	/// A filter for uncles within a block. This is for implementing
	/// further constraints on what uncles can be included, other than their ancestry.
	///
	/// For PoW, as long as the seals are checked, there is no need to use anything
	/// but the `VerifySeal` implementation as the filter. This is because the cost of making many equivocating
	/// uncles is high.
	///
	/// For PoS, there is no such limitation, so a further constraint must be imposed
	/// beyond a seal check in order to prevent an arbitrary number of
	/// equivocating uncles from being included.
	///
	/// The `OnePerAuthorPerHeight` filter is good for many slot-based PoS
	/// engines.
	type FilterUncle: FilterUncle<Self::Header, Self::AccountId>;
	/// An event handler for authored blocks.
	type EventHandler: EventHandler<Self::AccountId, Self::BlockNumber>;
}

/// An event handler for the authorship module. There is a dummy implementation
/// for `()`, which does nothing.
#[impl_trait_for_tuples::impl_for_tuples(30)]
pub trait EventHandler<Author, BlockNumber> {
	/// Note that the given account ID is the author of the current block.
	fn note_author(author: Author);

	/// Note that the given account ID authored the given uncle, and how many
	/// blocks older than the current block it is (age >= 0, so siblings are allowed)
	fn note_uncle(author: Author, age: BlockNumber);
}

/// Additional filtering on uncles that pass preliminary ancestry checks.
///
/// This should do work such as checking seals
pub trait FilterUncle<Header, Author> {
	/// An accumulator of data about uncles included.
	///
	/// In practice, this is used to validate uncles against others in the same block.
	type Accumulator: Default;

	/// Do additional filtering on a seal-checked uncle block, with the accumulated
	/// filter.
	fn filter_uncle(header: &Header, acc: &mut Self::Accumulator)
		-> Result<Option<Author>, &'static str>;
}

impl<H, A> FilterUncle<H, A> for () {
	type Accumulator = ();
	fn filter_uncle(_: &H, _acc: &mut Self::Accumulator)
		-> Result<Option<A>, &'static str>
	{
		Ok(None)
	}
}

/// A filter on uncles which verifies seals and does no additional checks.
/// This is well-suited to consensus modes such as PoW where the cost of
/// equivocating is high.
pub struct SealVerify<T>(rstd::marker::PhantomData<T>);

impl<Header, Author, T: VerifySeal<Header, Author>> FilterUncle<Header, Author>
	for SealVerify<T>
{
	type Accumulator = ();

	fn filter_uncle(header: &Header, _acc: &mut ())
		-> Result<Option<Author>, &'static str>
	{
		T::verify_seal(header)
	}
}

/// A filter on uncles which verifies seals and ensures that there is only
/// one uncle included per author per height.
///
/// This does O(n log n) work in the number of uncles included.
pub struct OnePerAuthorPerHeight<T, N>(rstd::marker::PhantomData<(T, N)>);

impl<Header, Author, T> FilterUncle<Header, Author>
	for OnePerAuthorPerHeight<T, Header::Number>
where
	Header: HeaderT + PartialEq,
	Header::Number: Ord,
	Author: Clone + PartialEq + Ord,
	T: VerifySeal<Header, Author>,
{
	type Accumulator = BTreeSet<(Header::Number, Author)>;

	fn filter_uncle(header: &Header, acc: &mut Self::Accumulator)
		-> Result<Option<Author>, &'static str>
	{
		let author = T::verify_seal(header)?;
		let number = header.number();

		if let Some(ref author) = author {
			if !acc.insert((number.clone(), author.clone())) {
				return Err("more than one uncle per number per author included");
			}
		}

		Ok(author)
	}
}

#[derive(Encode, Decode)]
#[cfg_attr(any(feature = "std", test), derive(PartialEq, Debug))]
enum UncleEntryItem<BlockNumber, Hash, Author> {
	InclusionHeight(BlockNumber),
	Uncle(Hash, Option<Author>),
}

decl_storage! {
	trait Store for Module<T: Trait> as Authorship {
		/// Uncles
		Uncles: Vec<UncleEntryItem<T::BlockNumber, T::Hash, T::AccountId>>;
		/// Author of current block.
		Author: Option<T::AccountId>;
		/// Whether uncles were already set in this block.
		DidSetUncles: bool;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn on_initialize(now: T::BlockNumber) {
			let uncle_generations = T::UncleGenerations::get();
			// prune uncles that are older than the allowed number of generations.
			if uncle_generations <= now {
				let minimum_height = now - uncle_generations;
				Self::prune_old_uncles(minimum_height)
			}

			<Self as Store>::DidSetUncles::put(false);

			T::EventHandler::note_author(Self::author());
		}

		fn on_finalize() {
			// ensure we never go to trie with these values.
			<Self as Store>::Author::kill();
			<Self as Store>::DidSetUncles::kill();
		}

		/// Provide a set of uncles.
		#[weight = SimpleDispatchInfo::FixedOperational(10_000)]
		fn set_uncles(origin, new_uncles: Vec<T::Header>) -> DispatchResult {
			ensure_none(origin)?;

			if <Self as Store>::DidSetUncles::get() {
				return Err("Uncles already set in block.");
			}
			<Self as Store>::DidSetUncles::put(true);

			Self::verify_and_import_uncles(new_uncles)
		}
	}
}

impl<T: Trait> Module<T> {
	/// Fetch the author of the block.
	///
	/// This is safe to invoke in `on_initialize` implementations, as well
	/// as afterwards.
	pub fn author() -> T::AccountId {
		// Check the memoized storage value.
		if let Some(author) = <Self as Store>::Author::get() {
			return author;
		}

		let digest = <system::Module<T>>::digest();
		let pre_runtime_digests = digest.logs.iter().filter_map(|d| d.as_pre_runtime());
		if let Some(author) = T::FindAuthor::find_author(pre_runtime_digests) {
			<Self as Store>::Author::put(&author);
			author
		} else {
			Default::default()
		}
	}

	fn verify_and_import_uncles(new_uncles: Vec<T::Header>) -> DispatchResult {
		let now = <system::Module<T>>::block_number();

		let mut uncles = <Self as Store>::Uncles::get();
		uncles.push(UncleEntryItem::InclusionHeight(now));

		let mut acc: <T::FilterUncle as FilterUncle<_, _>>::Accumulator = Default::default();

		for uncle in new_uncles {
			let prev_uncles = uncles.iter().filter_map(|entry|
				match entry {
					UncleEntryItem::InclusionHeight(_) => None,
					UncleEntryItem::Uncle(h, _) => Some(h),
				});
			let author = Self::verify_uncle(&uncle, prev_uncles, &mut acc)?;
			let hash = uncle.hash();

			T::EventHandler::note_uncle(
				author.clone().unwrap_or_default(),
				now - uncle.number().clone(),
			);
			uncles.push(UncleEntryItem::Uncle(hash, author));
		}

		<Self as Store>::Uncles::put(&uncles);
		Ok(())
	}

	fn verify_uncle<'a, I: IntoIterator<Item=&'a T::Hash>>(
		uncle: &T::Header,
		existing_uncles: I,
		accumulator: &mut <T::FilterUncle as FilterUncle<T::Header, T::AccountId>>::Accumulator,
	) -> Result<Option<T::AccountId>, &'static str>
	{
		let now = <system::Module<T>>::block_number();

		let (minimum_height, maximum_height) = {
			let uncle_generations = T::UncleGenerations::get();
			let min = if now >= uncle_generations {
				now - uncle_generations
			} else {
				Zero::zero()
			};

			(min, now)
		};

		let hash = uncle.hash();

		if uncle.number() < &One::one() {
			return Err("uncle is genesis");
		}

		if uncle.number() > &maximum_height {
			return Err("uncle is too high in chain");
		}

		{
			let parent_number = uncle.number().clone() - One::one();
			let parent_hash = <system::Module<T>>::block_hash(&parent_number);
			if &parent_hash != uncle.parent_hash() {
				return Err("uncle parent not in chain");
			}
		}

		if uncle.number() < &minimum_height {
			return Err("uncle not recent enough to be included");
		}

		let duplicate = existing_uncles.into_iter().find(|h| **h == hash).is_some();
		let in_chain = <system::Module<T>>::block_hash(uncle.number()) == hash;

		if duplicate || in_chain {
			return Err("uncle already included")
		}

		// check uncle validity.
		T::FilterUncle::filter_uncle(&uncle, accumulator)
	}

	fn prune_old_uncles(minimum_height: T::BlockNumber) {
		let mut uncles = <Self as Store>::Uncles::get();
		let prune_entries = uncles.iter().take_while(|item| match item {
			UncleEntryItem::Uncle(_, _) => true,
			UncleEntryItem::InclusionHeight(height) => height < &minimum_height,
		});
		let prune_index = prune_entries.count();

		let _ = uncles.drain(..prune_index);
		<Self as Store>::Uncles::put(uncles);
	}
}

impl<T: Trait> ProvideInherent for Module<T> {
	type Call = Call<T>;
	type Error = MakeFatalError<()>;
	const INHERENT_IDENTIFIER: InherentIdentifier = INHERENT_IDENTIFIER;

	fn create_inherent(data: &InherentData) -> Option<Self::Call> {
		let uncles = data.uncles().unwrap_or_default();
		let mut set_uncles = Vec::new();

		if !uncles.is_empty() {
			let prev_uncles = <Self as Store>::Uncles::get();
			let mut existing_hashes: Vec<_> = prev_uncles.into_iter().filter_map(|entry|
				match entry {
					UncleEntryItem::InclusionHeight(_) => None,
					UncleEntryItem::Uncle(h, _) => Some(h),
				}
			).collect();

			let mut acc: <T::FilterUncle as FilterUncle<_, _>>::Accumulator = Default::default();

			for uncle in uncles {
				match Self::verify_uncle(&uncle, &existing_hashes, &mut acc) {
					Ok(_) => {
						let hash = uncle.hash();
						set_uncles.push(uncle);
						existing_hashes.push(hash);
					}
					Err(_) => {
						// skip this uncle
					}
				}
			}
		}

		if set_uncles.is_empty() {
			None
		} else {
			Some(Call::set_uncles(set_uncles))
		}
	}

	fn check_inherent(_call: &Self::Call, _data: &InherentData) -> result::Result<(), Self::Error> {
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::with_externalities;
	use primitives::{H256, Blake2Hasher};
	use sr_primitives::traits::{BlakeTwo256, IdentityLookup};
	use sr_primitives::testing::Header;
	use sr_primitives::generic::DigestItem;
	use sr_primitives::Perbill;
	use support::{parameter_types, impl_outer_origin, ConsensusEngineId};

	impl_outer_origin!{
		pub enum Origin for Test {}
	}

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;

	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: u32 = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}

	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Call = ();
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type WeightMultiplierUpdate = ();
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type AvailableBlockRatio = AvailableBlockRatio;
		type MaximumBlockLength = MaximumBlockLength;
		type Version = ();
	}

	parameter_types! {
		pub const UncleGenerations: u64 = 5;
	}

	impl Trait for Test {
		type FindAuthor = AuthorGiven;
		type UncleGenerations = UncleGenerations;
		type FilterUncle = SealVerify<VerifyBlock>;
		type EventHandler = ();
	}

	type System = system::Module<Test>;
	type Authorship = Module<Test>;

	const TEST_ID: ConsensusEngineId = [1, 2, 3, 4];

	pub struct AuthorGiven;

	impl FindAuthor<u64> for AuthorGiven {
		fn find_author<'a, I>(digests: I) -> Option<u64>
			where I: 'a + IntoIterator<Item=(ConsensusEngineId, &'a [u8])>
		{
			for (id, data) in digests {
				if id == TEST_ID {
					return u64::decode(&mut &data[..]).ok();
				}
			}

			None
		}
	}

	pub struct VerifyBlock;

	impl VerifySeal<Header, u64> for VerifyBlock {
		fn verify_seal(header: &Header) -> Result<Option<u64>, &'static str> {
			let pre_runtime_digests = header.digest.logs.iter().filter_map(|d| d.as_pre_runtime());
			let seals = header.digest.logs.iter().filter_map(|d| d.as_seal());

			let author = match AuthorGiven::find_author(pre_runtime_digests) {
				None => return Err("no author"),
				Some(author) => author,
			};

			for (id, seal) in seals {
				if id == TEST_ID {
					match u64::decode(&mut &seal[..]) {
						Err(_) => return Err("wrong seal"),
						Ok(a) => {
							if a != author {
								return Err("wrong author in seal");
							}
							break
						}
					}
				}
			}

			Ok(Some(author))
		}
	}

	fn seal_header(mut header: Header, author: u64) -> Header {
		{
			let digest = header.digest_mut();
			digest.logs.push(DigestItem::PreRuntime(TEST_ID, author.encode()));
			digest.logs.push(DigestItem::Seal(TEST_ID, author.encode()));
		}

		header
	}

	fn create_header(number: u64, parent_hash: H256, state_root: H256) -> Header {
		Header::new(
			number,
			Default::default(),
			state_root,
			parent_hash,
			Default::default(),
		)
	}

	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		let t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		t.into()
	}

	#[test]
	fn prune_old_uncles_works() {
		use UncleEntryItem::*;
		with_externalities(&mut new_test_ext(), || {
			let hash = Default::default();
			let author = Default::default();
			let uncles = vec![
				InclusionHeight(1u64), Uncle(hash, Some(author)), Uncle(hash, None), Uncle(hash, None),
				InclusionHeight(2u64), Uncle(hash, None),
				InclusionHeight(3u64), Uncle(hash, None),
			];

			<Authorship as Store>::Uncles::put(uncles);
			Authorship::prune_old_uncles(3);

			let uncles = <Authorship as Store>::Uncles::get();
			assert_eq!(uncles, vec![InclusionHeight(3u64), Uncle(hash, None)]);
		})
	}

	#[test]
	fn rejects_bad_uncles() {
		with_externalities(&mut new_test_ext(), || {
			let author_a = 69;

			struct CanonChain {
				inner: Vec<Header>,
			}

			impl CanonChain {
				fn best_hash(&self) -> H256 {
					self.inner.last().unwrap().hash()
				}

				fn canon_hash(&self, index: usize) -> H256 {
					self.inner[index].hash()
				}

				fn header(&self, index: usize) -> &Header {
					&self.inner[index]
				}

				fn push(&mut self, header: Header) {
					self.inner.push(header)
				}
			}

			let mut canon_chain = CanonChain {
				inner: vec![seal_header(create_header(0, Default::default(), Default::default()), 999)],
			};

			for number in 1..8 {
				System::initialize(&number, &canon_chain.best_hash(), &Default::default(), &Default::default());
				let header = seal_header(System::finalize(), author_a);
				canon_chain.push(header);
			}

			// initialize so system context is set up correctly.
			System::initialize(&8, &canon_chain.best_hash(), &Default::default(), &Default::default());

			// 2 of the same uncle at once
			{
				let uncle_a = seal_header(
					create_header(3, canon_chain.canon_hash(2), [1; 32].into()),
					author_a,
				);
				assert_eq!(
					Authorship::verify_and_import_uncles(vec![uncle_a.clone(), uncle_a.clone()]),
					Err("uncle already included"),
				);
			}

			// 2 of the same uncle at different times.
			{
				let uncle_a = seal_header(
					create_header(3, canon_chain.canon_hash(2), [1; 32].into()),
					author_a,
				);

				assert!(Authorship::verify_and_import_uncles(vec![uncle_a.clone()]).is_ok());

				assert_eq!(
					Authorship::verify_and_import_uncles(vec![uncle_a.clone()]),
					Err("uncle already included"),
				);
			}

			// same uncle as ancestor.
			{
				let uncle_clone = canon_chain.header(5).clone();

				assert_eq!(
					Authorship::verify_and_import_uncles(vec![uncle_clone]),
					Err("uncle already included"),
				);
			}

			// uncle without valid seal.
			{
				let unsealed = create_header(3, canon_chain.canon_hash(2), [2; 32].into());
				assert_eq!(
					Authorship::verify_and_import_uncles(vec![unsealed]),
					Err("no author"),
				);
			}

			// old uncles can't get in.
			{
				assert_eq!(System::block_number(), 8);

				let gen_2 = seal_header(
					create_header(2, canon_chain.canon_hash(1), [3; 32].into()),
					author_a,
				);

				assert_eq!(
					Authorship::verify_and_import_uncles(vec![gen_2]),
					Err("uncle not recent enough to be included"),
				);
			}

			// siblings are also allowed
			{
				let other_8 = seal_header(
					create_header(8, canon_chain.canon_hash(7), [1; 32].into()),
					author_a,
				);

				assert!(Authorship::verify_and_import_uncles(vec![other_8]).is_ok());
			}
		});
	}

	#[test]
	fn sets_author_lazily() {
		with_externalities(&mut new_test_ext(), || {
			let author = 42;
			let mut header = seal_header(
				create_header(1, Default::default(), [1; 32].into()),
				author,
			);

			header.digest_mut().pop(); // pop the seal off.
			System::initialize(&1, &Default::default(), &Default::default(), header.digest());

			assert_eq!(Authorship::author(), author);
		});
	}

	#[test]
	fn one_uncle_per_author_per_number() {
		type Filter = OnePerAuthorPerHeight<VerifyBlock, u64>;

		let author_a = 42;
		let author_b = 43;

		let mut acc: <Filter as FilterUncle<Header, u64>>::Accumulator = Default::default();
		let header_a1 = seal_header(
			create_header(1, Default::default(), [1; 32].into()),
			author_a,
		);
		let header_b1 = seal_header(
			create_header(1, Default::default(), [1; 32].into()),
			author_b,
		);

		let header_a2_1 = seal_header(
			create_header(2, Default::default(), [1; 32].into()),
			author_a,
		);
		let header_a2_2 = seal_header(
			create_header(2, Default::default(), [2; 32].into()),
			author_a,
		);

		let mut check_filter = move |uncle| {
			Filter::filter_uncle(uncle, &mut acc)
		};

		// same height, different author is OK.
		assert_eq!(check_filter(&header_a1), Ok(Some(author_a)));
		assert_eq!(check_filter(&header_b1), Ok(Some(author_b)));

		// same author, different height.
		assert_eq!(check_filter(&header_a2_1), Ok(Some(author_a)));

		// same author, same height (author a, height 2)
		assert!(check_filter(&header_a2_2).is_err());
	}
}
