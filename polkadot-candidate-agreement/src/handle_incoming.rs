// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! A stream that handles incoming messages to the BFT agreement module and statement
//! table. It forwards as necessary, and dispatches requests for determining availability
//! and validity of candidates as necessary.

use std::collections::HashSet;

use futures::prelude::*;
use futures::stream::{Fuse, FuturesUnordered};
use futures::sync::mpsc;

use table::{self, Statement, Context as TableContext};

use super::{Context, CheckedMessage, SharedTable, TypeResolve};

enum CheckResult {
	Available,
	Unavailable,
	Valid,
	Invalid,
}

enum Checking<D, A, V> {
	Availability(D, A),
	Validity(D, V),
}

impl<D, A, V, E> Future for Checking<D, A, V>
	where
		D: Clone,
		A: Future<Item=bool,Error=E>,
		V: Future<Item=bool,Error=E>,
{
	type Item = (D, CheckResult);
	type Error = E;

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		Ok(Async::Ready(match *self {
			Checking::Availability(ref digest, ref mut f) => {
				match try_ready!(f.poll()) {
					true => (digest.clone(), CheckResult::Available),
					false => (digest.clone(), CheckResult::Unavailable),
				}
			}
			Checking::Validity(ref digest, ref mut f) => {
				match try_ready!(f.poll()) {
					true => (digest.clone(), CheckResult::Valid),
					false => (digest.clone(), CheckResult::Invalid),
				}
			}
		}))
	}
}

/// Handles incoming messages to the BFT service and statement table.
///
/// Also triggers requests for determining validity and availability of other
/// parachain candidates.
pub struct HandleIncoming<C: Context, I> {
	table: SharedTable<C>,
	messages_in: Fuse<I>,
	bft_out: mpsc::UnboundedSender<<C as TypeResolve>::BftCommunication>,
	local_id: C::AuthorityId,
	requesting_about: FuturesUnordered<Checking<
		C::Digest,
		<C::CheckAvailability as IntoFuture>::Future,
		<C::CheckCandidate as IntoFuture>::Future,
	>>,
	checked_validity: HashSet<C::Digest>,
	checked_availability: HashSet<C::Digest>,
}

impl<C: Context, I> HandleIncoming<C, I> {
	fn sign_and_import_statement(&self, digest: C::Digest, result: CheckResult) {
		let statement = match result {
			CheckResult::Valid => Statement::Valid(digest),
			CheckResult::Invalid => Statement::Invalid(digest),
			CheckResult::Available => Statement::Available(digest),
			CheckResult::Unavailable => return, // no such statement and not provable.
		};

		// TODO: trigger broadcast to peers immediately?
		self.table.sign_and_import(statement);
	}

	fn import_message(&mut self, origin: C::AuthorityId, message: CheckedMessage<C>) {
		match message {
			CheckedMessage::Bft(msg) => { let _ = self.bft_out.unbounded_send(msg); }
			CheckedMessage::Table(table_messages) => {
				// import all table messages and check for any that we
				// need to produce statements for.
				let msg_iter = table_messages
					.into_iter()
					.map(|m| (m, Some(origin.clone())));
				let summaries: Vec<_> = self.table.import_statements(msg_iter);

				for summary in summaries {
					self.dispatch_on_summary(summary)
				}
			}
		}
	}

	// on new candidates in our group, begin checking validity.
	// on new candidates in our availability sphere, begin checking availability.
	fn dispatch_on_summary(&mut self, summary: table::Summary<C::Digest, C::GroupId>) {
		let is_validity_member =
			self.table.context().is_member_of(&self.local_id, &summary.group_id);

		let is_availability_member =
			self.table.context().is_availability_guarantor_of(&self.local_id, &summary.group_id);

		let digest = &summary.candidate;

		// TODO: consider a strategy based on the number of candidate votes as well.
		let checking_validity =
			is_validity_member &&
			self.checked_validity.insert(digest.clone()) &&
			self.table.proposed_digest() != Some(digest.clone());

		let checking_availability = is_availability_member && self.checked_availability.insert(digest.clone());

		if checking_validity || checking_availability {
			let context = &*self.table.context();
			let requesting_about = &mut self.requesting_about;
			self.table.with_candidate(digest, |c| match c {
				None => {} // TODO: handle table inconsistency somehow?
				Some(candidate) => {
					if checking_validity {
						let future = context.check_validity(candidate).into_future();
						let checking = Checking::Validity(digest.clone(), future);
						requesting_about.push(checking);
					}

					if checking_availability {
						let future = context.check_availability(candidate).into_future();
						let checking = Checking::Availability(digest.clone(), future);
						requesting_about.push(checking);
					}
				}
			})
		}
	}
}

impl<C, I, E> HandleIncoming<C, I>
	where
		C: Context,
		I: Stream<Item=(C::AuthorityId, CheckedMessage<C>),Error=E>,
		C::CheckAvailability: IntoFuture<Error=E>,
		C::CheckCandidate: IntoFuture<Error=E>,
{
	pub fn new(
		table: SharedTable<C>,
		messages_in: I,
		bft_out: mpsc::UnboundedSender<<C as TypeResolve>::BftCommunication>,
	) -> Self {
		let local_id = table.context().local_id();

		HandleIncoming {
			table,
			bft_out,
			local_id,
			messages_in: messages_in.fuse(),
			requesting_about: FuturesUnordered::new(),
			checked_validity: HashSet::new(),
			checked_availability: HashSet::new(),
		}
	}
}

impl<C, I, E> Future for HandleIncoming<C, I>
	where
		C: Context,
		I: Stream<Item=(C::AuthorityId, CheckedMessage<C>),Error=E>,
		C::CheckAvailability: IntoFuture<Error=E>,
		C::CheckCandidate: IntoFuture<Error=E>,
{
	type Item = ();
	type Error = E;

	fn poll(&mut self) -> Poll<(), E> {
		loop {
			// FuturesUnordered is safe to poll after it has completed.
			while let Async::Ready(Some((d, r))) = self.requesting_about.poll()? {
				self.sign_and_import_statement(d, r);
			}

			match try_ready!(self.messages_in.poll()) {
				None => if self.requesting_about.is_empty() {
					return Ok(Async::Ready(()))
				} else {
					return Ok(Async::NotReady)
				},
				Some((origin, msg)) => self.import_message(origin, msg),
			}
		}
	}
}
