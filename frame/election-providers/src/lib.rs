#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
pub mod offchain;
pub mod onchain;

use sp_arithmetic::PerThing;
use sp_npos_elections::{ExtendedBalance, FlatSupportMap};
use sp_runtime::RuntimeDebug;
// TODO: maybe we can have this be generic in the trait? probably in the future.
use sp_npos_elections::VoteWeight;

/// Something that can compute the result of an election and pass it back to a pallet.
pub trait ElectionProvider<AccountId> {
	/// Elect a new set of winners.
	///
	/// The result is returned in a target major format, namely as a support map.
	fn elect<P: PerThing>(
		to_elect: usize,
		targets: Vec<AccountId>,
		voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
	) -> Result<FlatSupportMap<AccountId>, Error>
	where
		// TODO: Okay about these two, I get that we probably need the first one, but can't we
		// alleviate the latter one? I think we can say that all PerThing are Mul of some types.
		// Perhaps it is time to move the PerBill macros to something better? Yeah I think then we
		// can get rid of both of these types everywhere.
		ExtendedBalance: From<<P as PerThing>::Inner>,
		P: sp_std::ops::Mul<ExtendedBalance, Output = ExtendedBalance>;

	/// Returns true if an election is still ongoing.
	fn ongoing() -> bool;
}

#[derive(RuntimeDebug, Eq, PartialEq)]
pub enum Error {
	ElectionFailed,
	Internal(sp_npos_elections::Error),
}

impl From<sp_npos_elections::Error> for Error {
	fn from(err: sp_npos_elections::Error) -> Self {
		Error::Internal(err)
	}
}
