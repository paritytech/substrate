// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Some helper macros for this crate.

#[macro_export]
macro_rules! log {
	($level:tt, $patter:expr $(, $values:expr)* $(,)?) => {
		frame_support::debug::$level!(
			target: crate::LOG_TARGET,
			$patter $(, $values)*
		)
	};
}

#[macro_export]
macro_rules! voter_index_fn {
	($voters:ident, $acc:ty) => {
		|who: &$acc| -> Option<$crate::two_phase::VoterIndex> {
					$voters
						.iter()
						.position(|(x, _, _)| x == who)
						.and_then(|i| <usize as $crate::TryInto<$crate::two_phase::VoterIndex>>::try_into(i).ok())
					}
	};
}

#[macro_export]
macro_rules! target_index_fn {
	($targets:ident, $acc:ty) => {
		|who: &$acc| -> Option<$crate::two_phase::TargetIndex> {
					$targets
						.iter()
						.position(|x| x == who)
						.and_then(|i| <usize as $crate::TryInto<$crate::two_phase::TargetIndex>>::try_into(i).ok())
					}
	};
}

// TODO: these can use a cache.
#[macro_export]
macro_rules! stake_of_fn {
	($voters:ident, $acc:ty) => {
		|who: &$acc| -> $crate::VoteWeight {
							$voters
								.iter()
								.find(|(x, _, _)| x == who)
								.map(|(_, x, _)| *x)
								.unwrap_or_default()
							}
	};
}
