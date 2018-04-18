// Copyright 2017 Parity Technologies (UK) Ltd.
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

use primitives::block;
use super::*;
use super::error::*;

#[derive(Default)]
struct DummyTxPool {
	submitted: Vec<block::Extrinsic>,
}

impl AsyncAuthorApi for DummyTxPool {
	/// Submit extrinsic for inclusion in block.
	fn submit_extrinsic(&mut self, xt: Extrinsic) -> Result<()> {
		if self.submitted.len() < 1 {
			self.submitted.push(xt);
			Ok(())
		} else {
			Err(ErrorKind::PoolError.into())
		}
	}
}

#[test]
fn submit_transaction_should_not_cause_error() {
	let p = Arc::new(Mutex::new(DummyTxPool::default()));

	assert_matches!(
		AuthorApi::submit_extrinsic(&p, block::Extrinsic(vec![])),
		Ok(())
	);
	assert!(
		AuthorApi::submit_extrinsic(&p, block::Extrinsic(vec![])).is_err()
	);
}
