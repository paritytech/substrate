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

//! Some helper functions/macros for this crate.

#[macro_export]
macro_rules! log {
	($level:tt, $patter:expr $(, $values:expr)* $(,)?) => {
		frame_support::debug::$level!(
			target: $crate::LOG_TARGET,
			concat!("🏦 ", $patter) $(, $values)*
		)
	};
}

#[deprecated = "May only be used for benchmarking purposes."]
#[macro_export]
macro_rules! voter_index_fn_linear {
	(let $name:ident, $voters:ident, $t:ident) => {
		let $name = |who: &<$t as frame_system::Config>::AccountId| -> Option<$crate::CompactVoterIndexOf<$t>> {
			$voters
				.iter()
				.position(|(x, _, _)| x == who)
				.and_then(|i| <usize as $crate::sp_std::convert::TryInto<$crate::CompactVoterIndexOf<$t>>>::try_into(i).ok())
		};
	};
}

#[macro_export]
macro_rules! voter_index_generate_cache {
	($name:ident, $voters:ident, $t:ident) => {
		let mut $name:
			$crate::sp_std::collections::btree_map::BTreeMap<
				<$t as frame_system::Config>::AccountId,
				usize
			>
			= $crate::sp_std::collections::btree_map::BTreeMap::new();
		$voters.iter().enumerate().for_each(|(i, (x, _, _))| {
			let _existed = $name.insert(x.clone(), i);
			// if a duplicate exists, we only consider the last one. Defensive only, should never happen.
			debug_assert!(_existed.is_none());
		});
	};
}

#[macro_export]
macro_rules! voter_index_fn {
	(let $name:ident, $voters:ident, $t:ident) => {
		voter_index_generate_cache!(voters_map, $voters, $t);
		let $name = |who: &<$t as frame_system::Config>::AccountId| -> Option<CompactVoterIndexOf<$t>> {
			voters_map
				.get(who)
				.and_then(|i| <usize as $crate::sp_std::convert::TryInto<CompactVoterIndexOf<$t>>>::try_into(*i).ok())
		};
	};
}

#[macro_export]
macro_rules! voter_index_fn_usize {
	(let $name:ident, $voters:ident, $t:ident) => {
		voter_index_generate_cache!(voters_map, $voters, $t);
						let $name = |who: &<$t as frame_system::Config>::AccountId| -> Option<usize> {
							voters_map.get(who).cloned()
						};
	};
}

#[macro_export]
macro_rules! target_index_fn {
	(let $name: ident, $targets:ident, $t:ident) => {
		let $name = |who: &<$t as frame_system::Config>::AccountId| -> Option<$crate::CompactTargetIndexOf<$t>> {
			$targets
				.iter()
				.position(|x| x == who)
				.and_then(|i|
					<
						usize
						as
						$crate::sp_std::convert::TryInto<$crate::CompactTargetIndexOf<$t>>
					>::try_into(i).ok()
				)
		};
	};
}

#[macro_export]
macro_rules! voter_at_fn {
	(let $name:ident, $snap:ident, $t:ident) => {
		let $name = |i: $crate::CompactVoterIndexOf<$t>| -> Option<<$t as frame_system::Config>::AccountId> {
			<$crate::CompactVoterIndexOf<$t> as $crate::sp_std::convert::TryInto<usize>>::try_into(i)
				.ok()
				.and_then(|i| $snap
					.get(i)
					.map(|(x, _, _)| x)
					.cloned()
				)
		};
	};
}

#[macro_export]
macro_rules! target_at_fn {
	(let $name:ident, $snap:ident, $t:ident) => {
		let $name = |i: $crate::CompactTargetIndexOf<$t>| -> Option<<$t as frame_system::Config>::AccountId> {
			<
				$crate::CompactTargetIndexOf<$t>
				as
				$crate::sp_std::convert::TryInto<usize>
			>::try_into(i)
				.ok()
				.and_then(|i| $snap.get(i).cloned())
		};
	};
}

#[deprecated = "May only be used for benchmarking purposes."]
#[macro_export]
macro_rules! stake_of_fn_linear {
	(let $name:ident, $voters:ident, $t:ty) => {
		let $name = |who: &<$t as frame_system::Config>::AccountId| -> $crate::VoteWeight {
							$voters
								.iter()
								.find(|(x, _, _)| x == who)
								.map(|(_, x, _)| *x)
								.unwrap_or_default()
						};
	};
}

#[macro_export]
macro_rules! stake_of_fn {
	(let $name:ident, $voters:ident, $t:ty) => {
		let mut stake_map:
			$crate::sp_std::collections::btree_map::BTreeMap<
				<$t as frame_system::Config>::AccountId,
				VoteWeight,
			>
			= $crate::sp_std::collections::btree_map::BTreeMap::new();
		$voters.iter().for_each(|(x, y, _)| {
			let _existed = stake_map.insert(x.clone(), *y);
			// if a duplicate exists, we only consider the last one. Defensive only, should never happen.
			debug_assert!(_existed.is_none());
		});
		let $name = |who: &<$t as frame_system::Config>::AccountId| -> $crate::VoteWeight {
			stake_map
				.get(who)
				.cloned()
				.unwrap_or_default()
		};
	};
}
