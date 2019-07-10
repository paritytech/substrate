//! Niklas temp file

use parity_codec::{Decode, Encode};
use primitives::sr25519;
use runtime_support::{
	StorageValue, dispatch::Result, decl_module, decl_storage, decl_event,
	traits::{KeyOwnerProofSystem, ReportSlash, DoSlash, MisbehaviorKind}
};
use runtime_primitives::traits::Hash;
use std::marker::PhantomData;

// tmp
type FullId<T, Key> = <<T as Trait>::KeyOwner as KeyOwnerProofSystem<Key>>::FullIdentification;
type Key = sr25519::Public;

/// Trait for reporting slashes
pub trait Trait: srml_system::Trait {
	/// Key owner
    type KeyOwner: KeyOwnerProofSystem<Key>;
    /// Type of slash
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
		).expect("fixme");

		//check headers

		let hash = T::Hashing::hash_of(&proof.author);
		T::EquivocationSlash::slash(hash, identification);
	}
}

decl_storage! {
	trait Store for RollingMisconduct<T: Trait> as Rolling {
		/// Misbehavior reports
		MisconductReports: Vec<(u64, u64)>;
	}
}

decl_module! {
	pub struct RollingMisconduct<T: Trait> for enum Call where origin: T::Origin { }
}


impl<T: Trait> RollingMisconduct<T> {
	// On startup make sure no misconducts are reported
    fn on_initialize() {
		MisconductReports::mutate(|mr| {
			mr.clear();
		});
    }

	// Remove items that doesn't fit into the rolling window
    fn on_finalize() {
		const DUMMY_WINDOW_LENGTH: usize = 100;

		MisconductReports::mutate(|mr| {
			if mr.len() > DUMMY_WINDOW_LENGTH {
				let remove = mr.len() - DUMMY_WINDOW_LENGTH;
				mr.drain(..remove);
			}
		});
    }

    // note a misbehavior of `kind` and return the number of times it's happened
    // (including now) in the rolling window.
    fn report_misbehavior(base: u64, kind: u64) -> u64 {
		MisconductReports::mutate(|mr| {
			mr.push((base, kind));
			mr.iter().filter(|(_, k)| k == &kind).count() as u64
		})
    }
}

struct MyMisconduct<T, DoSlash> {
	_t: PhantomData<T>,
	ds: PhantomData<DoSlash>,
}

impl<T, DoSlash> MyMisconduct<T, DoSlash> {
	fn kind() -> u64 {
		0
	}

	fn base_severity() -> u64 {
		0
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
		let severity = RollingMisconduct::<T>::report_misbehavior(base_seve, kind);
		DS::do_slash(who, severity);
	}
}
