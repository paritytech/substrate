use serde_derive::Serialize;
use srml_support::runtime_primitives::traits::Digest;
use srml_support::codec::{Encode, Decode};
use primitives::H256;

pub trait Trait: 'static + Eq + Clone {
	type Origin: Into<Option<RawOrigin<Self::AccountId>>> + From<RawOrigin<Self::AccountId>>;
	type BlockNumber: Decode + Encode + Clone + Default;
	type Digest: Digest<Hash = H256>;
	type Hash;
	type AccountId: Encode + Decode;
	type Event: From<Event>;
	type Log: From<Log<Self>> + Into<DigestItemOf<Self>>;
}

pub type DigestItemOf<T> = <<T as Trait>::Digest as Digest>::Item;

srml_support::decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		pub fn deposit_event(_event: T::Event) {
		}
	}
}
impl<T: Trait> Module<T> {
	pub fn deposit_log(_item: <T::Digest as Digest>::Item) {
		unimplemented!();
	}
}

srml_support::decl_event!(
	pub enum Event {
		ExtrinsicSuccess,
		ExtrinsicFailed,
	}
);

/// Origin for the system module.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum RawOrigin<AccountId> {
	Root,
	Signed(AccountId),
	Inherent,
}

impl<AccountId> From<Option<AccountId>> for RawOrigin<AccountId> {
	fn from(s: Option<AccountId>) -> RawOrigin<AccountId> {
		match s {
			Some(who) => RawOrigin::Signed(who),
			None => RawOrigin::Inherent,
		}
	}
}

pub type Origin<T> = RawOrigin<<T as Trait>::AccountId>;

pub type Log<T> = RawLog<
	<T as Trait>::Hash,
>;

#[cfg_attr(feature = "std", derive(Serialize, Debug))]
#[derive(Encode, Decode, PartialEq, Eq, Clone)]
pub enum RawLog<H> {
	ChangesTrieRoot(H),
}

pub fn ensure_root<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<(), &'static str>
	where OuterOrigin: Into<Option<RawOrigin<AccountId>>>
{
	match o.into() {
		Some(RawOrigin::Root) => Ok(()),
		_ => Err("bad origin: expected to be a root origin"),
	}
}