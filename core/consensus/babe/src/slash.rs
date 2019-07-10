//! Niklas temp file

use parity_codec::{Decode, Encode};
use primitives::sr25519;

use runtime_support::{
	StorageValue, StorageMap, EnumerableStorageMap, dispatch::Result, decl_module, decl_storage, decl_event,
	traits::{KeyOwnerProofSystem, ReportSlash, DoSlash, MisbehaviorKind}
};
use runtime_primitives::{Perbill, traits::Hash};
use std::marker::PhantomData;

// tmp
type FullId<T, Key> = <<T as Trait>::KeyOwner as KeyOwnerProofSystem<Key>>::FullIdentification;
type Key = sr25519::Public;

const DEFAULT_WINDOW_LENGTH: u64 = 100;

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
		).expect("fixme");

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
		// TODO(niklasad1): This is not very good because it doesn't
		// _really_ works porportially w.r.t. to the session it happend in
		// just the window will be shrinked when it exceeds to threshold
		//
		// On the other hand, one could have
		// Kind -> Vec<SessionIndex> but then the problem is that
		// `SessionIndex` is a counter that is wrapping and might be
		// hard to determine which is `fresh`
		MisconductReports get(kind): linked_map Kind => Counter;

		/// Rolling window length (we need different windows for different kinds)
		WindowLength get(w) config(): u64 = DEFAULT_WINDOW_LENGTH;

		/// Some misconduct need to keep track of duplicate misconducts
		/// Such as only one is counted in the same session and so on.
		///
		// TODO(niklasad1): implement...
		SlashDeduplicator get(sd) config(): u64 = DEFAULT_WINDOW_LENGTH;
	}
}

decl_module! {
	pub struct RollingMisconduct<T: Trait> for enum Call where origin: T::Origin { }
}


impl<T: Trait> RollingMisconduct<T> {
	/// On startup make sure no misconducts are reported
    pub fn on_initialize() {}

	/// Set rolling window length
	pub fn set_window_length(len: u64) {
		WindowLength::put(len);
	}

	/// Remove items that doesn't fit into the rolling window
    pub fn on_session_end() {
		let max_window = WindowLength::get();

		// dummy thing lets assume that exactly 20 kinds
		for kind in 0..20 {
			MisconductReports::mutate(kind, |w| std::cmp::min(max_window, *w));
		}
    }

	/// Report misbehaviour for a misconduct kind
	///
	/// Return number of misbehavior in the current window
    pub fn report_misbehavior(kind: u64) -> u64 {
		MisconductReports::mutate(kind, |w| w.saturating_add(1));
		MisconductReports::get(kind)
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
		let severity = RollingMisconduct::<T>::report_misbehavior(kind);
		DS::do_slash(who, 0);
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
