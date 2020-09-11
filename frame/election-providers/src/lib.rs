
#![cfg_attr(not(feature = "std"), no_std)]

pub mod offchain;
pub mod onchain;

use sp_npos_elections::{ExtendedBalance, SupportMap};
use sp_arithmetic::PerThing;

/// Something that can compute the result of an election and pass it back to a pallet.
pub trait ElectionProvider<AccountId , VoteWeight> {
	/// Elect a new set of winners.
	///
	/// The result is returned in a target major format, namely as a support map.
	fn elect<P: PerThing>(
		to_elect: usize,
		candidates: Vec<AccountId>,
		voters: Vec<(AccountId, VoteWeight, Vec<AccountId>)>,
	) -> Result<SupportMap<AccountId>, Error> where
		// TODO: Okay about these two, I get that we probably need the first one, but can't we
		// alleviate the latter one? I think we can say that all PerThing are Mul of some types.
		// Perhaps it is time to move the PerBill macros to something better? Yeah I think then we
		// can get rid of both of these types everywhere.
		ExtendedBalance: From<<P as PerThing>::Inner>,
		P: sp_std::ops::Mul<ExtendedBalance, Output = ExtendedBalance>;
}

pub enum Error {
	ElectionFailed,
}

