// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use sc_network_test::Block;
use sp_core::H256;
use sp_runtime::traits::NumberFor;

use beefy_primitives::{crypto::Public, ValidatorSet};

use super::Rounds;
use crate::keystore::tests::Keyring;

#[test]
fn new_rounds() {
	sp_tracing::try_init_simple();

	let rounds = Rounds::<H256, NumberFor<Block>>::new(ValidatorSet::<Public>::empty());

	assert_eq!(0, rounds.validator_set_id());
	assert!(rounds.validators().is_empty());

	let validators = ValidatorSet::<Public> {
		validators: vec![Keyring::Alice.public(), Keyring::Bob.public(), Keyring::Charlie.public()],
		id: 42,
	};

	let rounds = Rounds::<H256, NumberFor<Block>>::new(validators);

	assert_eq!(42, rounds.validator_set_id());

	assert_eq!(
		vec![Keyring::Alice.public(), Keyring::Bob.public(), Keyring::Charlie.public()],
		rounds.validators()
	);
}

#[test]
fn add_vote() {
	sp_tracing::try_init_simple();

	let validators = ValidatorSet::<Public> {
		validators: vec![Keyring::Alice.public(), Keyring::Bob.public(), Keyring::Charlie.public()],
		id: Default::default(),
	};

	let rounds = Rounds::<H256, NumberFor<Block>>::new(validators);
}
