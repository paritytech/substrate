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
//! automatically "chill" validators and nominators upon a slash event, requiring them
//! to re-enlist voluntarily (acknowledging the slash) and begin a new slashing span.
//!
//! Based on research at https://research.web3.foundation/en/latest/polkadot/slashing/npos/

use super::{EraIndex, Trait, Module};
use codec::{HasCompact, Encode, Decode};

// A range of start..end eras for a slashing span.
#[derive(Encode, Decode)]
#[cfg_attr(test, derive(Debug, PartialEq))]
struct SlashingSpan {
	start: EraIndex,
	length: Option<EraIndex>, // the ongoing slashing span has indeterminate length.
}

/// An encoding of all of a nominator's slashing spans.
#[derive(Default, Encode, Decode)]
pub struct SlashingSpans {
	// the start era of the most recent (ongoing) slashing span.
	last_start: EraIndex,
	// all prior slashing spans start indices, in reverse order (most recent first)
	// encoded as offsets relative to the slashing span after it.
	prior: Vec<EraIndex>,
}

impl SlashingSpans {
	// an iterator over all slashing spans in _reverse_ order - most recent first.
	fn iter(&'_ self) -> impl Iterator<Item = SlashingSpan> + '_ {
		let mut last_start = self.last_start;
		let last = SlashingSpan { start: last_start, length: None };
		let prior = self.prior.iter().cloned().map(move |length| {
			let start = last_start - length;
			last_start = start;

			SlashingSpan { start, length: Some(length) }
		});

		rstd::iter::once(last).chain(prior)
	}

	// prune the slashing spans against a window, whose start era index is given.
	fn prune(&mut self, window_start: EraIndex) {
		let old_idx = self.iter()
			.skip(1) // skip ongoing span.
			.position(|span| span.length.map_or(false, |len| span.start + len <= window_start));

		if let Some(o) = old_idx {
			self.prior.truncate(o);
		}

		// readjust the ongoing span, if it started before the beginning of the winow.
		self.last_start = rstd::cmp::max(self.last_start, window_start);
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn single_slashing_span() {
		let spans = SlashingSpans {
			last_start: 1000,
			prior: Vec::new(),
		};

		assert_eq!(spans.iter().collect::<Vec<_>>(), vec![SlashingSpan { start: 1000, length: None }]);
	}

	#[test]
	fn many_prior_spans() {
		let spans = SlashingSpans {
			last_start: 1000,
			prior: vec![10, 9, 8, 10],
		};

		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { start: 1000, length: None },
				SlashingSpan { start: 990, length: Some(10) },
				SlashingSpan { start: 981, length: Some(9) },
				SlashingSpan { start: 973, length: Some(8) },
				SlashingSpan { start: 963, length: Some(10) },
			],
		)
	}

	#[test]
	fn pruning_spans() {
		let mut spans = SlashingSpans {
			last_start: 1000,
			prior: vec![10, 9, 8, 10],
		};

		spans.prune(981);
		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { start: 1000, length: None },
				SlashingSpan { start: 990, length: Some(10) },
				SlashingSpan { start: 981, length: Some(9) },
			],
		);

		spans.prune(982);
		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { start: 1000, length: None },
				SlashingSpan { start: 990, length: Some(10) },
				SlashingSpan { start: 981, length: Some(9) },
			],
		);

		spans.prune(989);
		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { start: 1000, length: None },
				SlashingSpan { start: 990, length: Some(10) },
				SlashingSpan { start: 981, length: Some(9) },
			],
		);

		spans.prune(1000);
		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { start: 1000, length: None },
			],
		);

		spans.prune(2000);
		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { start: 2000, length: None },
			],
		);

		// now all in one shot.
		let mut spans = SlashingSpans {
			last_start: 1000,
			prior: vec![10, 9, 8, 10],
		};
		spans.prune(2000);
		assert_eq!(
			spans.iter().collect::<Vec<_>>(),
			vec![
				SlashingSpan { start: 2000, length: None },
			],
		);
	}
}
