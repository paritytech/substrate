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
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

//! Build the contract module part of the genesis block storage.

use {Trait, ContractFee, CallBaseFee, CreateBaseFee, GasPrice, MaxDepth};

use runtime_primitives;
use runtime_io::{self, twox_128};
use runtime_support::StorageValue;
use codec::Encode;
use std::collections::HashMap;
use substrate_primitives::KeccakHasher;

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct GenesisConfig<T: Trait> {
	pub contract_fee: T::Balance,
	pub call_base_fee: T::Gas,
	pub create_base_fee: T::Gas,
	pub gas_price: T::Balance,
	pub max_depth: u32,
}

impl<T: Trait> runtime_primitives::BuildStorage for GenesisConfig<T> {
	fn build_storage(self) -> ::std::result::Result<HashMap<Vec<u8>, Vec<u8>>, String> {
		let r: runtime_io::TestExternalities<KeccakHasher> = map![
			twox_128(<ContractFee<T>>::key()).to_vec() => self.contract_fee.encode(),
			twox_128(<CallBaseFee<T>>::key()).to_vec() => self.call_base_fee.encode(),
			twox_128(<CreateBaseFee<T>>::key()).to_vec() => self.create_base_fee.encode(),
			twox_128(<GasPrice<T>>::key()).to_vec() => self.gas_price.encode(),
			twox_128(<MaxDepth<T>>::key()).to_vec() => self.max_depth.encode()
		];
		Ok(r.into())
	}
}
