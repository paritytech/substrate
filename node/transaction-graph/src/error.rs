// Copyright 2018 Parity Technologies (UK) Ltd.
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

use sr_primitives::transaction_validity::TransactionPriority as Priority;

error_chain! {
	errors {
		/// The transaction is already in the pool.
		AlreadyImported {
			description("Transaction is already in the pool."),
			display("Already imported"),
		}
		/// The transaction cannot be imported cause it's a replacement and has too low priority.
		TooLowPriority(old: Priority, new: Priority) {
			description("The priority is too low to replace transactions already in the pool."),
			display("Too low priority ({} > {})", old, new)
		}
		/// Deps cycle detected and we couldn't import transaction.
		CycleDetected {
			description("Transaction was not imported because of detected cycle."),
			display("Cycle Detected"),
		}
	}
}
