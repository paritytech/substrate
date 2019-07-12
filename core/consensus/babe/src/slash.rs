//! Niklas temp file

use parity_codec::{Decode, Encode};
use primitives::sr25519;

use srml_rolling_window::Module as RollingWindow;
use std::marker::PhantomData;
use runtime_support::traits::{KeyOwnerProofSystem, ReportSlash, DoSlash, Misbehavior};
use runtime_primitives::{Perbill, traits::Hash};

type FullId<T, K> = <<T as Trait>::KeyOwner as KeyOwnerProofSystem<K>>::FullIdentification;

/// Trait for reporting slashes
pub trait Trait: srml_system::Trait {
	/// Key that identifies the owner
    type KeyOwner: KeyOwnerProofSystem<sr25519::Public>;
    /// Type of slashing
	///
	/// FullId - is the full identification of the entity to slash
	/// which may be (AccountId, Exposure)
	type EquivocationSlash: ReportSlash<Self::Hash, FullId<Self, sr25519::Public>>;
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
	/// Create a new Babe equivocation proof
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

		// Assumption: author in the context __is__ the validator/authority that has voted/signed
		// two blocks in the same round
		let hash = T::Hashing::hash_of(&proof.author);

		T::EquivocationSlash::slash(hash, identification);
	}
}

pub struct MyMisconduct<T, DoSlash>((PhantomData<T>, PhantomData<DoSlash>));

// do this more elegant with some macro
// preferable with some linkage to the `misbehavior kind` ideally
impl<T, DoSlash> MyMisconduct<T, DoSlash> {
	fn kind() -> Misbehavior {
		Misbehavior::BabeEquivocation
	}

	fn base_severity() -> Perbill {
		Perbill::from_rational_approximation(1_u32, 100_u32)
	}
}

impl<T, Who, DS> ReportSlash<T::Hash, Who> for MyMisconduct<T, DS>
where
	T: Trait + srml_rolling_window::Trait<Kind = Misbehavior>,
	DS: DoSlash<Who, Perbill>,
{
	fn slash(footprint: T::Hash, who: Who) {
		let kind = Self::kind();
		let base_seve = Self::base_severity();
		RollingWindow::<T>::report_misbehavior(kind, footprint);

		let num_violations = match RollingWindow::<T>::get_misbehaved_unique(kind) {
			// if non-registered kind was registered (probably a bug)
			// don't slash in that case...
			None => return,
			Some(v) => v,
		};

		// number of validators
		let n = 50;

		// example how to estimate severity
		let severity = if num_violations < 10 {
			base_seve
		} else if num_violations < 1000 {
			// 3k / n^2
			// ignore base severity because `Permill` doesn't provide addition, e.g. (base + estimate)
			Perbill::from_rational_approximation(3 * num_violations, n*n)
		} else {
			Perbill::one()
		};

		DS::do_slash(who, severity);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use srml_system as system;
	use runtime_primitives::traits::{BlakeTwo256, IdentityLookup};
	use runtime_primitives::testing::{H256, Header};
	use runtime_support::{impl_outer_origin, parameter_types};

	pub type AccountId = u64;
	pub type Exposure = u64;

	#[derive(Clone, PartialEq, Eq, Debug)]
	pub struct Test;

	parameter_types! {
		pub const BlockHashCount: u64 = 250;
	}

	impl_outer_origin!{
		pub enum Origin for Test {}
	}

	impl srml_rolling_window::Trait for Test {
		type Kind = Misbehavior;
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
		type BlockHashCount = BlockHashCount;
	}

	impl Trait for Test {
		type KeyOwner = FakeSlasher<Self>;
		type EquivocationSlash = MyMisconduct<Self, FakeSlasher<Self>>;
	}

	pub struct FakeSlasher<T>(PhantomData<T>);

	impl<T: Trait> DoSlash<(T::AccountId, Exposure), Perbill> for FakeSlasher<T> {
		fn do_slash(_: (T::AccountId, Exposure), _severity: Perbill) {
			// does nothing ...
		}
	}

	impl<T: Trait> KeyOwnerProofSystem<sr25519::Public> for FakeSlasher<T> {
		type Proof = Vec<u8>;
		type FullIdentification = (T::AccountId, Exposure);

		fn prove(key: sr25519::Public) -> Option<Self::Proof> {
			Some(Vec::new())
		}

		fn check_proof(key: sr25519::Public, proof: Self::Proof) -> Option<Self::FullIdentification> {
			Some((Default::default(), 0))
		}
	}

	#[test]
	fn foo() {

		let eq = EquivocationProof::new(
			Default::default(),
			Default::default(),
			Default::default(),
			Vec::new(),
		);

		BabeSlashReporter::<Test>::report_equivocation(eq);
	}
}
