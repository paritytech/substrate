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

//! A slashing implementation for NPoS systems.
//!
//! For the purposes of the economic model, it is easiest to think of each validator
//! of a nominator which nominates only its own identity.
//!
//! The act of nomination signals intent to unify economic identity with the validator - to take part in the
//! rewards of a job well done, and to take part in the punishment of a job done badly.
//!
//! There are 3 main difficulties to account for with slashing in NPoS:
//!   - A nominator can nominate multiple validators and be slashed via any of them.
//!   - Until slashed, stake is reused from era to era. Nominating with N coins for E eras in a row
//!     does not mean you have N*E coins to be slashed - you've only ever had N.
//!   - Slashable offences can be found after the fact and out of order.
//!
//! The algorithm implemented in this module tries to balance these 3 difficulties.
//!
//! First, we only slash participants for the _maximum_ slash they receive in some time period,
//! rather than the sum. This ensures a protection from overslashing.
//!
//! Second, we do not want the time period (or "span") that the maximum is computed
//! over to last indefinitely. That would allow participants to begin acting with
//! impunity after some point, fearing no further repercussions. For that reason, we
//! automatically "chill" validators and withdraw a nominator's nomination after a slashing event,
//! requiring them to re-enlist voluntarily (acknowledging the slash) and begin a new
//! slashing span.
//!
//! Typically, you will have a single slashing event per slashing span. Only in the case
//! where a validator releases many misbehaviors at once
//!
//! Based on research at https://research.web3.foundation/en/latest/polkadot/slashing/npos/

use super::{EraIndex, Trait, Module, Store, BalanceOf, Exposure, Perbill, SessionInterface};
use sr_primitives::traits::{Zero, Saturating};
use support::{StorageValue, StorageMap, StorageDoubleMap, traits::{Currency, OnUnbalanced}};
use codec::{Encode, Decode};

/// The index of a slashing span - unique to each stash.
pub(crate) type SpanIndex = u32;

// A range of start..end eras for a slashing span.
#[derive(Encode, Decode)]
#[cfg_attr(test, derive(Debug, PartialEq))]
pub(crate) struct SlashingSpan {
	pub(crate) index: SpanIndex,
	pub(crate) start: EraIndex,
	pub(crate) length: Option<EraIndex>, // the ongoing slashing span has indeterminate length.
}

impl SlashingSpan {
	fn contains_era(&self, era: EraIndex) -> bool {
		self.start <= era && self.length.map_or(true, |l| self.start + l > era)
	}
}

/// An encoding of all of a nominator's slashing spans.
#[derive(Encode, Decode)]
pub struct SlashingSpans {
	// the index of the current slashing span of the nominator. different for
	// every stash, resets when the account hits free balance 0.
	span_index: SpanIndex,
	// the start era of the most recent (ongoing) slashing span.
	last_start: EraIndex,
	// all prior slashing spans start indices, in reverse order (most recent first)
	// encoded as offsets relative to the slashing span after it.
	prior: Vec<EraIndex>,
}

impl SlashingSpans {
	// creates a new record of slashing spans for a stash, starting at the beginning
	// of the bonding period, relative to now.
	fn new(window_start: EraIndex) -> Self {
		SlashingSpans {
			span_index: 0,
			last_start: window_start,
			prior: Vec::new(),
		}
	}

	// update the slashing spans to reflect the start of a new span at the era after `now`
	// returns `true` if a new span was started, `false` otherwise. `false` indicates
	// that internal state is unchanged.
	fn end_span(&mut self, now: EraIndex) -> bool {
		let next_start = now + 1;
		if next_start <= self.last_start { return false }

		let last_length = next_start - self.last_start;
		self.prior.insert(0, last_length);
		self.last_start = next_start;
		self.span_index += 1;
		true
	}

	// an iterator over all slashing spans in _reverse_ order - most recent first.
	pub(crate) fn iter(&'_ self) -> impl Iterator<Item = SlashingSpan> + '_ {
		let mut last_start = self.last_start;
		let mut index = self.span_index;
		let last = SlashingSpan { index, start: last_start, length: None };
		let prior = self.prior.iter().cloned().map(move |length| {
			let start = last_start - length;
			last_start = start;
			index -= 1;

			SlashingSpan { index, start, length: Some(length) }
		});

		rstd::iter::once(last).chain(prior)
	}

	// prune the slashing spans against a window, whose start era index is given.
	//
	// If this returns `Some`, then it includes a range start..end of all the span
	// indices which were pruned.
	fn prune(&mut self, window_start: EraIndex) -> Option<(SpanIndex, SpanIndex)> {
		let old_idx = self.iter()
			.skip(1) // skip ongoing span.
			.position(|span| span.length.map_or(false, |len| span.start + len <= window_start));

		let earliest_span_index = self.span_index - self.prior.len() as SpanIndex;
		let pruned = match old_idx {
			Some(o) => {
				self.prior.truncate(o);
				let new_earliest = self.span_index - self.prior.len() as SpanIndex;
				Some((earliest_span_index, new_earliest))
			}
			None => None,
		};

		// readjust the ongoing span, if it started before the beginning of the winow.
		self.last_start = rstd::cmp::max(self.last_start, window_start);
		pruned
	}
}

/// Parameters for performing a slash.
#[derive(Clone)]
pub(crate) struct SlashParams<'a, T: 'a + Trait> {
	/// The stash account being slashed.
	pub(crate) stash: &'a T::AccountId,
	/// The proportion of the slash.
	pub(crate) slash: Perbill,
	/// The exposure of the stash and all nominators.
	pub(crate) exposure: &'a Exposure<T::AccountId, BalanceOf<T>>,
	/// The era where the offence occurred.
	pub(crate) slash_era: EraIndex,
	/// The first era in the current bonding period.
	pub(crate) window_start: EraIndex,
	/// The current era.
	pub(crate) now: EraIndex,
}

/// Slash a validator and their nominators, if necessary.
pub(crate) fn slash<T: Trait>(params: SlashParams<T>){
	let SlashParams {
		stash,
		slash,
		exposure,
		slash_era,
		window_start,
		now,
	} = params.clone();

	// is the slash amount here a maximum for the era?
	let own_slash = slash * exposure.own;
	let (prior_slash_p, era_slash) = <Module<T> as Store>::ValidatorSlashInEra::get(
		&slash_era,
		stash,
	).unwrap_or((Perbill::zero(), Zero::zero()));

	if own_slash > era_slash {
		<Module<T> as Store>::ValidatorSlashInEra::insert(
			&slash_era,
			stash,
			&(slash, own_slash),
		);
	} else {
		// we slash based on the max in era - this new event is not the max,
		// so neither the validator or any nominators will need an update.
		return
	}

	// apply slash to validator.
	let mut spans = fetch_spans::<T>(stash, window_start);

	let target_span = spans.compare_and_update_span_slash(
		slash_era,
		own_slash,
	);

	if target_span == Some(spans.span_index()) {
		// misbehavior occurred within the current slashing span - take appropriate
		// actions.

		// chill the validator - it misbehaved in the current span and should
		// not continue in the next election. also end the slashing span.
		spans.end_span(now);
		<Module<T>>::chill_stash(stash);

		// make sure to disable validator till the end of this session
		if T::SessionInterface::disable_validator(stash).unwrap_or(false) {
			// force a new era, to select a new validator set
			crate::ForceEra::put(crate::Forcing::ForceNew);
		}
	}

	slash_nominators::<T>(params, prior_slash_p)
}

fn slash_nominators<T: Trait>(params: SlashParams<T>, prior_slash_p: Perbill) {
	let SlashParams {
		stash: _,
		slash,
		exposure,
		slash_era,
		window_start,
		now,
	} = params;

	for nominator in &exposure.others {
		let stash = &nominator.who;

		// the era slash of a nominator always grows, if the validator
		// had a new max slash for the era.
		let era_slash = {
			let own_slash_prior = prior_slash_p * nominator.value;
			let own_slash_by_validator = slash * nominator.value;
			let own_slash_difference = own_slash_by_validator.saturating_sub(own_slash_prior);

			let mut era_slash = <Module<T> as Store>::NominatorSlashInEra::get(
				&slash_era,
				stash,
			).unwrap_or(Zero::zero());

			era_slash += own_slash_difference;

			<Module<T> as Store>::NominatorSlashInEra::insert(
				&slash_era,
				stash,
				&era_slash,
			);

			era_slash
		};

		// compare the era slash against other eras in the same span.
		let mut spans = fetch_spans::<T>(stash, window_start);

		let target_span = spans.compare_and_update_span_slash(
			slash_era,
			era_slash,
		);

		if target_span == Some(spans.span_index()) {
			// Chill the nominator outright, ending the slashing span.
			spans.end_span(now);
			<Module<T>>::chill_stash(&stash);
		}
	}
}

// helper struct for managing a set of spans we are currently inspecting.
// writes alterations to disk on drop, but only if a slash has been carried out.
//
// NOTE: alterations to slashing metadata should not be done after this is dropped.
// dropping this struct applies any necessary slashes, which can lead to free balance
// being 0, and the account being garbage-collected -- a dead account should get no new
// metadata.
struct InspectingSpans<'a, T: Trait + 'a> {
	dirty: bool,
	window_start: EraIndex,
	stash: &'a T::AccountId,
	spans: SlashingSpans,
	deferred_slashes: Vec<LazySlash<T>>,
	_marker: rstd::marker::PhantomData<T>,
}

// fetches the slashing spans record for a stash account, initializing it if necessary.
fn fetch_spans<T: Trait>(stash: &T::AccountId, window_start: EraIndex) -> InspectingSpans<T> {
	let spans = <Module<T> as Store>::SlashingSpans::get(stash).unwrap_or_else(|| {
		let spans = SlashingSpans::new(window_start);
		<Module<T> as Store>::SlashingSpans::insert(stash, &spans);
		spans
	});

	InspectingSpans {
		dirty: false,
		window_start,
		stash,
		spans,
		deferred_slashes: Vec::with_capacity(1), // we usually would only slash once.
		_marker: rstd::marker::PhantomData,
	}
}

impl<'a, T: 'a + Trait> InspectingSpans<'a, T> {
	fn span_index(&self) -> SpanIndex {
		self.spans.span_index
	}

	fn end_span(&mut self, now: EraIndex) {
		self.dirty = self.spans.end_span(now) || self.dirty;
	}

	// compares the slash in an era to the overall current span slash.
	// if it's higher, applies the difference of the slashes and then updates the span on disk.
	//
	// returns the span index of the era, if any, along with a slash to be lazily applied
	// when all book-keeping is done.
	fn compare_and_update_span_slash(
		&mut self,
		slash_era: EraIndex,
		slash: BalanceOf<T>,
	) -> Option<SpanIndex> {
		let target_span = self.spans.iter().find(|span| span.contains_era(slash_era))?;
		let span_slash_key = (self.stash.clone(), target_span.index);
		let span_slash = <Module<T>>::span_slash(&span_slash_key);

		if span_slash < slash {
			// new maximum span slash. apply the difference.
			let difference = slash - span_slash;

			self.dirty = true;
			<Module<T> as Store>::SpanSlash::insert(&span_slash_key, &slash);

			self.deferred_slashes.push(slash_lazy(self.stash.clone(), difference));
		}

		Some(target_span.index)
	}
}

impl<'a, T: 'a + Trait> Drop for InspectingSpans<'a, T> {
	fn drop(&mut self) {
		// only update on disk if we slashed this account.
		if !self.dirty { return }

		if let Some((start, end)) = self.spans.prune(self.window_start) {
			for span_index in start..end {
				<Module<T> as Store>::SpanSlash::remove(&(self.stash.clone(), span_index));
			}
		}

		<Module<T> as Store>::SlashingSpans::insert(self.stash, &self.spans);
	}
}

// perform a slash which is lazily applied on `Drop`. This allows us to register
// that the slash should happen without being in the middle of any bookkeeping.
fn slash_lazy<T: Trait>(stash: T::AccountId, value: BalanceOf<T>) -> LazySlash<T> {
	LazySlash { stash, value }
}

/// Clear slashing metadata for an obsolete era.
pub(crate) fn clear_era_metadata<T: Trait>(obsolete_era: EraIndex) {
	<Module<T> as Store>::ValidatorSlashInEra::remove_prefix(&obsolete_era);
	<Module<T> as Store>::NominatorSlashInEra::remove_prefix(&obsolete_era);
}

/// Clear slashing metadata for a dead account.
pub(crate) fn clear_stash_metadata<T: Trait>(stash: &T::AccountId) {
	let spans = match <Module<T> as Store>::SlashingSpans::take(stash) {
		None => return,
		Some(s) => s,
	};

	// kill slashing-span metadata for account.
	//
	// this can only happen while the account is staked _if_ they are completely slashed.
	// in that case, they may re-bond, but it would count again as span 0. Further ancient
	// slashes would slash into this new bond, since metadata has now been cleared.
	for span in spans.iter() {
		<Module<T> as Store>::SpanSlash::remove(&(stash.clone(), span.index));
	}
}

struct LazySlash<T: Trait> {
	stash: T::AccountId,
	value: BalanceOf<T>,
}

impl<T: Trait> Drop for LazySlash<T> {
	fn drop(&mut self) {
		let controller = match <Module<T>>::bonded(&self.stash) {
			None => return, // defensive: should always exist.
			Some(c) => c,
		};

		let mut ledger = match <Module<T>>::ledger(&controller) {
			Some(ledger) => ledger,
			None => return, // nothing to do.
		};

		let mut value = self.value.min(ledger.active);

		if !value.is_zero() {
			ledger.active -= value;

			// Avoid there being a dust balance left in the staking system.
			if ledger.active < T::Currency::minimum_balance() {
				value += ledger.active;
				ledger.active = Zero::zero();
			}

			ledger.total -= value;

			// TODO: rewards

			let (imbalance, _) = T::Currency::slash(&self.stash, value);
			T::Slash::on_unbalanced(imbalance);

			<Module<T>>::update_ledger(&controller, &ledger);

			// trigger the event
			<Module<T>>::deposit_event(
				super::RawEvent::Slash(self.stash.clone(), value)
			);
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn span_contains_era() {
		// unbounded end
		let span = SlashingSpan { index: 0, start: 1000, length: None };
		assert!(!span.contains_era(0));
		assert!(!span.contains_era(999));

		assert!(span.contains_era(1000));
		assert!(span.contains_era(1001));
		assert!(span.contains_era(10000));

		// bounded end - non-inclusive range.
		let span = SlashingSpan { index: 0, start: 1000, length: Some(10) };
		assert!(!span.contains_era(0));
		assert!(!span.contains_era(999));

		assert!(span.contains_era(1000));
		assert!(span.contains_era(1001));
		assert!(span.contains_era(1009));
		assert!(!span.contains_era(1010));
		assert!(!span.contains_era(1011));
	}

	#[test]
	fn single_slashing_span() {
		let spans = SlashingSpans {
			span_index: 0,
			last_start: 1000,
			prior: Vec::new(),
		};

		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![SlashingSpan { index: 0, start: 1000, length: None }],
		);
	}

	#[test]
	fn many_prior_spans() {
		let spans = SlashingSpans {
			span_index: 10,
			last_start: 1000,
			prior: vec![10, 9, 8, 10],
		};

		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { index: 10, start: 1000, length: None },
				SlashingSpan { index: 9, start: 990, length: Some(10) },
				SlashingSpan { index: 8, start: 981, length: Some(9) },
				SlashingSpan { index: 7, start: 973, length: Some(8) },
				SlashingSpan { index: 6, start: 963, length: Some(10) },
			],
		)
	}

	#[test]
	fn pruning_spans() {
		let mut spans = SlashingSpans {
			span_index: 10,
			last_start: 1000,
			prior: vec![10, 9, 8, 10],
		};

		assert_eq!(spans.prune(981), Some((6, 8)));
		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { index: 10, start: 1000, length: None },
				SlashingSpan { index: 9, start: 990, length: Some(10) },
				SlashingSpan { index: 8, start: 981, length: Some(9) },
			],
		);

		assert_eq!(spans.prune(982), None);
		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { index: 10, start: 1000, length: None },
				SlashingSpan { index: 9, start: 990, length: Some(10) },
				SlashingSpan { index: 8, start: 981, length: Some(9) },
			],
		);

		assert_eq!(spans.prune(989), None);
		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { index: 10, start: 1000, length: None },
				SlashingSpan { index: 9, start: 990, length: Some(10) },
				SlashingSpan { index: 8, start: 981, length: Some(9) },
			],
		);

		assert_eq!(spans.prune(1000), Some((8, 10)));
		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { index: 10, start: 1000, length: None },
			],
		);

		assert_eq!(spans.prune(2000), None);
		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { index: 10, start: 2000, length: None },
			],
		);

		// now all in one shot.
		let mut spans = SlashingSpans {
			span_index: 10,
			last_start: 1000,
			prior: vec![10, 9, 8, 10],
		};
		assert_eq!(spans.prune(2000), Some((6, 10)));
		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { index: 10, start: 2000, length: None },
			],
		);
	}

	#[test]
	fn ending_span() {
		let mut spans = SlashingSpans {
			span_index: 1,
			last_start: 10,
			prior: Vec::new(),
		};

		assert!(spans.end_span(10));

		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { index: 2, start: 11, length: None },
				SlashingSpan { index: 1, start: 10, length: Some(1) },
			],
		);

		assert!(spans.end_span(15));
		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { index: 3, start: 16, length: None },
				SlashingSpan { index: 2, start: 11, length: Some(5) },
				SlashingSpan { index: 1, start: 10, length: Some(1) },
			],
		);

		// does nothing if not a valid end.
		assert!(!spans.end_span(15));
		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { index: 3, start: 16, length: None },
				SlashingSpan { index: 2, start: 11, length: Some(5) },
				SlashingSpan { index: 1, start: 10, length: Some(1) },
			],
		);
	}
}
