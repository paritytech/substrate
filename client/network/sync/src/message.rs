// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Network packet message types. These get serialized and put into the lower level protocol
//! payload.

use sp_runtime::traits::Block as BlockT;

/// Type alias for using the BlockData type using block type parameters.
pub type BlockData<B> =
	generic::BlockData<<B as BlockT>::Header, <B as BlockT>::Hash, <B as BlockT>::Extrinsic>;

/// Generic types.
pub mod generic {
	use codec::{Decode, Encode};
	use sp_runtime::{EncodedJustification, Justifications};

	/// Block data sent in the response.
	#[derive(Debug, PartialEq, Eq, Clone, Encode, Decode)]
	pub struct BlockData<Header, Hash, Extrinsic> {
		/// Block header hash.
		pub hash: Hash,
		/// Block header if requested.
		pub header: Option<Header>,
		/// Block body if requested.
		pub body: Option<Vec<Extrinsic>>,
		/// Block body indexed transactions if requested.
		pub indexed_body: Option<Vec<Vec<u8>>>,
		/// Block receipt if requested.
		pub receipt: Option<Vec<u8>>,
		/// Block message queue if requested.
		pub message_queue: Option<Vec<u8>>,
		/// Justification if requested.
		pub justification: Option<EncodedJustification>,
		/// Justifications if requested.
		pub justifications: Option<Justifications>,
	}
}
