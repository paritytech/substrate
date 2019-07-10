//! Niklas temp file

use parity_codec::{Decode, Encode};
use primitives::sr25519;

use runtime_support::{
	StorageValue, StorageMap, EnumerableStorageMap, dispatch::Result, decl_module, decl_storage, decl_event,
	traits::{KeyOwnerProofSystem, ReportSlash, DoSlash, MisbehaviorKind}
};
use runtime_primitives::{Perbill, traits::{Hash, Header}};
use std::marker::PhantomData;

// tmp
type FullId<T, Key> = <<T as Trait>::KeyOwner as KeyOwnerProofSystem<Key>>::FullIdentification;
type Key = sr25519::Public;

const DEFAULT_WINDOW_LENGTH: u32 = 100;

/// Trait for reporting slashes
pub trait Trait: srml_system::Trait {
	/// Key that identifies the owner
    type KeyOwner: KeyOwnerProofSystem<Key>;
    /// Type of slashing
	///
	/// FullId - is the full identification of the entity to slash
	/// which should in most cases be (AccountId, Exposure)
	///
	///
	type EquivocationSlash: ReportSlash<Self::Hash, FullId<Self, Key>>;
}

/// Represents an Babe equivocation proof.
#[derive(Debug, Clone, Encode, Decode, PartialEq)]
pub struct EquivocationProof<H, Proof> {
	first_header: H,
	second_header: H,
	author: sr25519::Public,
	membership_proof: Proof,
}

impl<H, P> EquivocationProof<H, P> {
	/// Create a new Babe equivocation proof.
	pub fn new(
		first_header: H,
		second_header: H,
		author: sr25519::Public,
		membership_proof: P,
	) -> Self {
		Self {
			first_header,
			second_header,
			author,
			membership_proof,
		}
	}
}

/// Babe slash reporter
pub struct BabeSlashReporter<T>(PhantomData<T>);

impl<T: Trait> BabeSlashReporter<T> {

	/// Report an equivocation
	pub fn report_equivocation(
		proof: EquivocationProof<
			T::Hash,
			<<T as Trait>::KeyOwner as KeyOwnerProofSystem<sr25519::Public>>::Proof
		>,
	) {
		let identification = T::KeyOwner::check_proof(
			proof.author.clone(),
			proof.membership_proof
		).expect("mocked will always succeed; qed");

		//check headers

		let hash = T::Hashing::hash_of(&proof.author);
		T::EquivocationSlash::slash(hash, identification);
	}
}

type Kind = u64;
type Counter = u64;

decl_storage! {
	trait Store for RollingMisconduct<T: Trait> as R {
		/// Misbehavior reports
		///
		/// This have a weird edge-case when because `SessionIndex`
		/// is currently an u32 and may wrap around in that case.
		///
		/// Basically we have can detect that by checking if all
		/// session_indexes are bigger than the current session index
		MisconductReports get(kind): linked_map Kind => Vec<u32>;

		/// Rolling window length for different kinds
		WindowLength get(w) config(): map Kind => u32;

		/// Some misbehaviours may need to keep track concurrent misbehaviours
		/// by the same entity in the same session which is not possible currently
		///
		/// Because then we need to store `who`
		///
		// TODO(niklasad1): implement...
		SlashDeduplicator get(sd) config(): linked_map Kind => u32;
	}
}

decl_module! {
	pub struct RollingMisconduct<T: Trait> for enum Call where origin: T::Origin { }
}


impl<T: Trait> RollingMisconduct<T> {
	/// On startup make sure no misconducts are reported
    pub fn on_initialize() {
		for kind in 0..2 {
			WindowLength::insert(kind, DEFAULT_WINDOW_LENGTH);
		}
	}

	/// Remove items that doesn't fit into the rolling window
    pub fn on_session_end(session_index: u32) {

		// dummy thing to iterate over possible enum variants
		for kind in 0..2 {
			MisconductReports::mutate(kind, |window| {
				let max_window = WindowLength::get(kind);

				// edge-case session_index has wrapped-around
				if window.iter().all(|s| *s > session_index) {
					if let Some(idx) = window.iter().rev().position(|s| {
							let ss = u32::max_value() - s;
							ss - session_index + 1 > max_window as u32
					}) {
						window.drain(..window.len() - idx);
					}
				} else {
					if let Some(idx) = window.iter().position(|s| *s > session_index) {
						window.drain(..idx);
					}
				}
			});
		}
	}

	/// Report misbehaviour for a misconduct kind
	///
	/// Return number of misbehaviors in the current session
    pub fn report_misbehavior(kind: u64, session_index: u32) -> u64 {
		let window_length = WindowLength::get(kind);
		MisconductReports::mutate(kind, |w| w.push(session_index + window_length));
		MisconductReports::get(kind).len() as u64
    }
}

pub struct MyMisconduct<T, DoSlash>((PhantomData<T>, PhantomData<DoSlash>));

impl<T, DoSlash> MyMisconduct<T, DoSlash> {
	fn kind() -> u64 {
		0
	}

	fn base_severity() -> Perbill {
		Perbill::from_rational_approximation(1_u32, 100_u32)
	}
}

impl<T: Trait, Who, DS> ReportSlash<T::Hash, Who> for MyMisconduct<T, DS>
where
	DS: DoSlash<Who, u64>
{
	fn slash(_footprint: T::Hash, who: Who) {
		let kind = Self::kind();
		let base_seve = Self::base_severity();
		// do something special with severity
		// such as
		// if severity > BIG then slash something like 100%
		// else if severity > SMALL then compute some severity level and slash
		// if severity < LESS  -> slash little
		panic!("time to slash");
		let dummy_session_index = 0;
		let number_misbehaviours = RollingMisconduct::<T>::report_misbehavior(kind, dummy_session_index);
		DS::do_slash(who, number_misbehaviours);
	}
}


#[cfg(test)]
mod tests {
	use super::*;
	use srml_system as system;
	use runtime_primitives::traits::{BlakeTwo256, IdentityLookup};
	use runtime_primitives::testing::{H256, Header};
	use runtime_support::impl_outer_origin;

	pub type AccountId = u64;
	pub type Exposure = u64;

	#[derive(Clone, PartialEq, Eq, Debug)]
	pub struct Test;

	impl_outer_origin!{
		pub enum Origin for Test {}
	}

	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = AccountId;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
	}

	impl Trait for Test {
		type KeyOwner = FakeSlasher<Self>;
		type EquivocationSlash = MyMisconduct<Self, FakeSlasher<Self>>;
	}

	pub struct FakeSlasher<T>(PhantomData<T>);

	impl<T: Trait> DoSlash<(T::AccountId, Exposure), u64> for FakeSlasher<T> {
		fn do_slash(_: (T::AccountId, Exposure), _severity: u64) {
			// does nothing ...
		}
	}

	impl<T: Trait> KeyOwnerProofSystem<sr25519::Public> for FakeSlasher<T> {
		type Proof = Vec<u8>;
		type FullIdentification = (T::AccountId, u64);

		fn prove(key: Key) -> Option<Self::Proof> {
			Some(Vec::new())
		}

		fn check_proof(key: Key, proof: Self::Proof) -> Option<Self::FullIdentification> {
			Some((Default::default(), 0))
		}
	}

	#[test]
	fn foo() {

		let eq = EquivocationProof::new(
			H256::default(),
			H256::default(),
			Default::default(),
			Vec::new(),
		);

		BabeSlashReporter::<Test>::report_equivocation(eq);
	}
}
