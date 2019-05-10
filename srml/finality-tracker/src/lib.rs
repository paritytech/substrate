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

//! SRML module that tracks the last finalized block, as perceived by block authors.

#![cfg_attr(not(feature = "std"), no_std)]

#[macro_use]
extern crate srml_support;

use inherents::{
	RuntimeString, InherentIdentifier, ProvideInherent,
	InherentData, MakeFatalError,
};
use srml_support::StorageValue;
use primitives::traits::{As, One, Zero};
use rstd::{prelude::*, result, cmp, vec};
use parity_codec::Decode;
use srml_system::{ensure_none, Trait as SystemTrait};

#[cfg(feature = "std")]
use parity_codec::Encode;

const DEFAULT_WINDOW_SIZE: u64 = 101;
const DEFAULT_DELAY: u64 = 1000;

/// The identifier for the `finalnum` inherent.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"finalnum";

/// Auxiliary trait to extract finalized inherent data.
pub trait FinalizedInherentData<N: Decode> {
	/// Get finalized inherent data.
	fn finalized_number(&self) -> Result<N, RuntimeString>;
}

impl<N: Decode> FinalizedInherentData<N> for InherentData {
	fn finalized_number(&self) -> Result<N, RuntimeString> {
		self.get_data(&INHERENT_IDENTIFIER)
			.and_then(|r| r.ok_or_else(|| "Finalized number inherent data not found".into()))
	}
}

/// Provider for inherent data.
#[cfg(feature = "std")]
pub struct InherentDataProvider<F, N> {
	inner: F,
	_marker: std::marker::PhantomData<N>,
}

#[cfg(feature = "std")]
impl<F, N> InherentDataProvider<F, N> {
	pub fn new(final_oracle: F) -> Self {
		InherentDataProvider { inner: final_oracle, _marker: Default::default() }
	}
}

#[cfg(feature = "std")]
impl<F, N: Encode> inherents::ProvideInherentData for InherentDataProvider<F, N>
	where F: Fn() -> Result<N, RuntimeString>
{
	fn inherent_identifier(&self) -> &'static InherentIdentifier {
		&INHERENT_IDENTIFIER
	}

	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), RuntimeString> {
		(self.inner)()
			.and_then(|n| inherent_data.put_data(INHERENT_IDENTIFIER, &n))
	}

	fn error_to_string(&self, _error: &[u8]) -> Option<String> {
		Some(format!("no further information"))
	}
}


pub trait Trait: SystemTrait {
	/// Something which can be notified when the timestamp is set. Set this to `()` if not needed.
	type OnFinalizationStalled: OnFinalizationStalled<Self::BlockNumber>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Timestamp {
		/// Recent hints.
		RecentHints get(recent_hints) build(|_| vec![T::BlockNumber::zero()]): Vec<T::BlockNumber>;
		/// Ordered recent hints.
		OrderedHints get(ordered_hints) build(|_| vec![T::BlockNumber::zero()]): Vec<T::BlockNumber>;
		/// The median.
		Median get(median) build(|_| T::BlockNumber::zero()): T::BlockNumber;
		/// The number of recent samples to keep from this chain. Default is n-100
		pub WindowSize get(window_size) config(window_size): T::BlockNumber = T::BlockNumber::sa(DEFAULT_WINDOW_SIZE);
		/// The delay after which point things become suspicious.
		pub ReportLatency get(report_latency) config(report_latency): T::BlockNumber = T::BlockNumber::sa(DEFAULT_DELAY);

		/// Final hint to apply in the block. `None` means "same as parent".
		Update: Option<T::BlockNumber>;

		// when initialized through config this is set in the beginning.
		Initialized get(initialized) build(|_| false): bool;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Hint that the author of this block thinks the best finalized
		/// block is the given number.
		fn final_hint(origin, #[compact] hint: T::BlockNumber) {
			ensure_none(origin)?;
			assert!(!<Self as Store>::Update::exists(), "Final hint must be updated only once in the block");
			assert!(
				srml_system::Module::<T>::block_number() >= hint,
				"Finalized height above block number",
			);
			<Self as Store>::Update::put(hint);
		}

		fn on_finalize() {
			Self::update_hint(<Self as Store>::Update::take())
		}
	}
}

impl<T: Trait> Module<T> {
	fn update_hint(hint: Option<T::BlockNumber>) {
		if !Self::initialized() {
			<Self as Store>::RecentHints::put(vec![T::BlockNumber::zero()]);
			<Self as Store>::OrderedHints::put(vec![T::BlockNumber::zero()]);
			<Self as Store>::Median::put(T::BlockNumber::zero());

			<Self as Store>::Initialized::put(true);
		}

		let mut recent = Self::recent_hints();
		let mut ordered = Self::ordered_hints();
		let window_size = cmp::max(T::BlockNumber::one(), Self::window_size());

		let hint = hint.unwrap_or_else(|| recent.last()
			.expect("always at least one recent sample; qed").clone()
		);

		// prune off the front of the list -- typically 1 except for when
		// the sample size has just been shrunk.
		{
			// take into account the item we haven't pushed yet.
			let to_prune = (recent.len() + 1).saturating_sub(window_size.as_() as usize);

			for drained in recent.drain(..to_prune) {
				let idx = ordered.binary_search(&drained)
					.expect("recent and ordered contain the same items; qed");

				ordered.remove(idx);
			}
		}

		// find the position in the ordered list where the new item goes.
		let ordered_idx = ordered.binary_search(&hint)
			.unwrap_or_else(|idx| idx);

		ordered.insert(ordered_idx, hint);
		recent.push(hint);

		let two = T::BlockNumber::one() + T::BlockNumber::one();

		let median = {
			let len = ordered.len();
			assert!(len > 0, "pruning dictated by window_size which is always saturated at 1; qed");

			if len % 2 == 0 {
				let a = ordered[len / 2];
				let b = ordered[(len / 2) - 1];

				// compute average.
				(a + b) / two
			} else {
				ordered[len / 2]
			}
		};

		let our_window_size = recent.len();

		<Self as Store>::RecentHints::put(recent);
		<Self as Store>::OrderedHints::put(ordered);
		<Self as Store>::Median::put(median);

		if T::BlockNumber::sa(our_window_size as u64) == window_size {
			let now = srml_system::Module::<T>::block_number();
			let latency = Self::report_latency();

			// the delay is the latency plus half the window size.
			let delay = latency + (window_size / two);
			// median may be at most n - delay
			if median + delay <= now {
				T::OnFinalizationStalled::on_stalled(window_size - T::BlockNumber::one());
			}
		}
	}
}

/// Called when finalization stalled at a given number.
pub trait OnFinalizationStalled<N> {
	/// The parameter here is how many more blocks to wait before applying
	/// changes triggered by finality stalling.
	fn on_stalled(further_wait: N);
}

macro_rules! impl_on_stalled {
	() => (
		impl<N> OnFinalizationStalled<N> for () {
			fn on_stalled(_: N) {}
		}
	);

	( $($t:ident)* ) => {
		impl<NUM: Clone, $($t: OnFinalizationStalled<NUM>),*> OnFinalizationStalled<NUM> for ($($t,)*) {
			fn on_stalled(further_wait: NUM) {
				$($t::on_stalled(further_wait.clone());)*
			}
		}
	}
}

for_each_tuple!(impl_on_stalled);

impl<T: Trait> ProvideInherent for Module<T> {
	type Call = Call<T>;
	type Error = MakeFatalError<()>;
	const INHERENT_IDENTIFIER: InherentIdentifier = INHERENT_IDENTIFIER;

	fn create_inherent(data: &InherentData) -> Option<Self::Call> {
		let final_num =
			data.finalized_number().expect("Gets and decodes final number inherent data");

		// make hint only when not same as last to avoid bloat.
		Self::recent_hints().last().and_then(|last| if last == &final_num {
			None
		} else {
			Some(Call::final_hint(final_num))
		})
	}

	fn check_inherent(_call: &Self::Call, _data: &InherentData) -> result::Result<(), Self::Error> {
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use sr_io::{with_externalities, TestExternalities};
	use substrate_primitives::H256;
	use primitives::BuildStorage;
	use primitives::traits::{BlakeTwo256, IdentityLookup, OnFinalize, Header as HeaderT};
	use primitives::testing::{Digest, DigestItem, Header};
	use srml_support::impl_outer_origin;
	use srml_system as system;
	use lazy_static::lazy_static;
	use parking_lot::Mutex;

	#[derive(Clone, PartialEq, Debug)]
	pub struct StallEvent {
		at: u64,
		further_wait: u64,
	}

	macro_rules! make_test_context {
		() => {
			#[derive(Clone, Eq, PartialEq)]
			pub struct Test;

			impl_outer_origin! {
				pub enum Origin for Test {}
			}

			impl system::Trait for Test {
				type Origin = Origin;
				type Index = u64;
				type BlockNumber = u64;
				type Hash = H256;
				type Hashing = BlakeTwo256;
				type Digest = Digest;
				type AccountId = u64;
				type Lookup = IdentityLookup<u64>;
				type Header = Header;
				type Event = ();
				type Log = DigestItem;
			}

			type System = system::Module<Test>;

			lazy_static! {
				static ref NOTIFICATIONS: Mutex<Vec<StallEvent>> = Mutex::new(Vec::new());
			}

			pub struct StallTracker;
			impl OnFinalizationStalled<u64> for StallTracker {
				fn on_stalled(further_wait: u64) {
					let now = System::block_number();
					NOTIFICATIONS.lock().push(StallEvent { at: now, further_wait });
				}
			}

			impl Trait for Test {
				type OnFinalizationStalled = StallTracker;
			}

			type FinalityTracker = Module<Test>;
		}
	}

	#[test]
	fn median_works() {
		make_test_context!();
		let t = system::GenesisConfig::<Test>::default().build_storage().unwrap().0;

		with_externalities(&mut TestExternalities::new(t), || {
			FinalityTracker::update_hint(Some(500));
			assert_eq!(FinalityTracker::median(), 250);
			assert!(NOTIFICATIONS.lock().is_empty());
		});
	}

	#[test]
	fn notifies_when_stalled() {
		make_test_context!();
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap().0;
		t.extend(GenesisConfig::<Test> {
			window_size: 11,
			report_latency: 100
		}.build_storage().unwrap().0);

		with_externalities(&mut TestExternalities::new(t), || {
			let mut parent_hash = System::parent_hash();
			for i in 2..106 {
				System::initialize(&i, &parent_hash, &Default::default());
				FinalityTracker::on_finalize(i);
				let hdr = System::finalize();
				parent_hash = hdr.hash();
			}

			assert_eq!(
				NOTIFICATIONS.lock().to_vec(),
				vec![StallEvent { at: 105, further_wait: 10 }]
			)
		});
	}

	#[test]
	fn recent_notifications_prevent_stalling() {
		make_test_context!();
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap().0;
		t.extend(GenesisConfig::<Test> {
			window_size: 11,
			report_latency: 100
		}.build_storage().unwrap().0);

		with_externalities(&mut TestExternalities::new(t), || {
			let mut parent_hash = System::parent_hash();
			for i in 2..106 {
				System::initialize(&i, &parent_hash, &Default::default());
				assert_ok!(FinalityTracker::dispatch(
					Call::final_hint(i-1),
					Origin::NONE,
				));
				FinalityTracker::on_finalize(i);
				let hdr = System::finalize();
				parent_hash = hdr.hash();
			}

			assert!(NOTIFICATIONS.lock().is_empty());
		});
	}
}
