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
//! Based on research at https://research.web3.foundation/en/latest/polkadot/slashing/npos/

use super::{EraIndex, Trait, Module, Store, BalanceOf, Exposure, Perbill};
use sr_primitives::traits::Zero;
use support::{StorageValue, StorageMap, StorageDoubleMap};
use codec::{HasCompact, Encode, Decode};

/// The index of a slashing span - unique to each stash.
pub (crate) type SpanIndex = u32;

// A range of start..end eras for a slashing span.
#[derive(Encode, Decode)]
#[cfg_attr(test, derive(Debug, PartialEq))]
struct SlashingSpan {
	index: SpanIndex,
	start: EraIndex,
	length: Option<EraIndex>, // the ongoing slashing span has indeterminate length.
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

	fn bump_span(&mut self, now: EraIndex) {
		if now <= self.last_start { return }

		let last_length = now - self.last_start;
		self.prior.insert(0, last_length);
		self.last_start = now;
		self.span_index += 1;
	}

	// an iterator over all slashing spans in _reverse_ order - most recent first.
	fn iter(&'_ self) -> impl Iterator<Item = SlashingSpan> + '_ {
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
pub(crate) struct SlashParams<'a, T: 'a + Trait> {
	/// The stash account being slashed.
	pub(crate) stash: &'a T::AccountId,
	/// The proportion and total amount of the slash (proportion applied to `exposure.total`).
	pub(crate) slash: (Perbill, BalanceOf<T>),
	/// The exposure of the stash and all nominators.
	pub(crate) exposure: &'a Exposure<T::AccountId, BalanceOf<T>>,
	/// The era where the offence occurred.
	pub(crate) slash_era: EraIndex,
	/// The first era in the current bonding period.
	pub(crate) window_start: EraIndex,
}

/// Slash a validator and their nominators, if necessary.
pub(crate) fn slash<T: Trait>(params: SlashParams<T>){
	let SlashParams {
		stash,
		slash,
		exposure,
		slash_era,
		window_start,
	} = params;
	let (slash_proportion, slash_amount) = slash;

	// is the slash amount here a maximum for the era?
	let era_slash = <Module<T> as Store>::SlashInEra::get(&slash_era, stash)
		.map(|(_, amount)| amount)
		.unwrap_or(Zero::zero());

	if slash_amount > era_slash {
		<Module<T> as Store>::SlashInEra::insert(
			&slash_era,
			stash,
			&(slash_proportion, slash_amount),
		);
	} else {
		// we slash based on the max in era - this new event is not the max,
		// so neither the validator or any nominators will need an update.
		return
	}

	// what about the maximum slash in the span?
	let mut spans = <Module<T> as Store>::SlashingSpans::get(stash).unwrap_or_else(|| {
		SlashingSpans::new(window_start)
	});
	span_gc::<T>(stash, spans.prune(window_start));

	<Module<T> as Store>::SlashingSpans::insert(stash, &spans);

	let target_span = spans.iter().find(|span| span.contains_era(slash_era));
	let span_slash = <Module<T>>::span_slash(&(stash.clone(), target_span.index));

	let spans = spans;

	// `chill` validator if this is the most recent span.
	if spans.span_index == target_span.index {
		// TODO
	}

	// false if have chewed through all of our own exposure for this era,
	// true if nothing has been passed onto nominators.
	let has_own_remaining = slash_amount < exposure.own;

	let effective_nominator_slash = if slash_amount > span_slash {
		let remaining_slash = slash_amount - span_slash;
		let remaining_own = exposure.own.saturating_sub(span_slash);

		// divide up the slash into own and nominator portions.
		let (own_slash, nominator_slash) = if remaining_slash >= remaining_own {
			(remaining_own, remaining_slash - remaining_own)
		} else {
			(remaining_slash, 0)
		};

		// Apply `own_slash` to self balance. Since this is the highest slash of
		// the span, we actually apply the slash to our own bond.
		// TODO

		// note new highest slash in span
		<Module<T> as Store>::SpanSlash::insert(
			&(stash.clone(), target_span.index),
			&slash_amount,
		);

		nominator_slash
	} else {
		// this validator has already been slashed for more than `slash_amount` within
		// this slashing span. That means that we do not actually apply the slash on our own
		// bond, but if the nominator slash for this era is now non-zero we have
		// to pass that onwards to the nominator calculation.
		if has_own_remaining {
			0
		} else {
			slash_amount - exposure.own
		}
	};

	if effective_nominator_slash == 0 {
		// nominators are unaffected.
		return
	}

	// p_{v,e} is non-zero here - it is the ratio of the remaining slash in the era
	// to the amount of exposure held by nominators.
	let nominator_slash_proportion = {
		let d = Perbill::from_rational_approximation(
			effective_nominator_slash,
			exposure.total - exposure.own,
		);
		let d = Perbill::one() / (exposure.total - exposure.own);
		d * effective_nominator_slash;
	};

	// TODO: apply to nominators.
}

fn slash_nominators<T: Trait>() {

}

fn span_gc<T: Trait>(stash: &T::AccountId, pruned_range: Option<(SpanIndex, SpanIndex)>) {
	if let Some((start, end)) = pruned_range {
		for span_index in start..end {
			<Module<T> as Store>::SpanSlash::remove(&(stash.clone(), span_index));
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
}
