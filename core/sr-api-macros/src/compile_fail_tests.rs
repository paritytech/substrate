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

//! Compile fail tests.

mod declaring_own_block {
	/*!
	```compile_fail
		#[macro_use]
		extern crate substrate_client;
		extern crate sr_primitives as runtime_primitives;

		use runtime_primitives::traits::Block as BlockT;

		decl_runtime_apis! {
			pub trait Api<Block: BlockT> {
				fn test();
			}
		}

		fn main() {}
	```
	*/
}

mod declaring_own_block_with_different_name {
	/*!
	```compile_fail
		#[macro_use]
		extern crate substrate_client;
		extern crate sr_primitives as runtime_primitives;

		use runtime_primitives::traits::Block as BlockT;

		decl_runtime_apis! {
			pub trait Api<B: BlockT> {
				fn test();
			}
		}

		fn main() {}
	```
	*/
}

mod adding_self_parameter {
	/*!
	```compile_fail
		#[macro_use]
		extern crate substrate_client;
		extern crate sr_primitives as runtime_primitives;

		decl_runtime_apis! {
			pub trait Api {
				fn test(&self);
			}
		}

		fn main() {}
	```
	*/
}

mod adding_at_parameter {
	/*!
	```compile_fail
		#[macro_use]
		extern crate substrate_client;
		extern crate sr_primitives as runtime_primitives;

		decl_runtime_apis! {
			pub trait Api {
				fn test(at: u64);
			}
		}

		fn main() {}
	```
	*/
}

mod adding_parameter_with_type_reference {
	/*!
	```compile_fail
		#[macro_use]
		extern crate substrate_client;
		extern crate sr_primitives as runtime_primitives;

		decl_runtime_apis! {
			pub trait Api {
				fn test(data: &u64);
			}
		}

		fn main() {}
	```
	*/
}

mod missing_block_generic_parameter {
	/*!
	```compile_fail
		#[macro_use]
		extern crate substrate_client;
		extern crate sr_primitives as runtime_primitives;
		extern crate substrate_primitives as primitives;
		#[macro_use]
		extern crate parity_codec_derive;
		extern crate serde;
		extern crate core;

		use primitives::hash::H256;
		use runtime_primitives::traits::{BlakeTwo256, GetNodeBlockType, Extrinsic as ExtrinsicT};

		// All the stuff we need to declare our `Block`
		pub type BlockNumber = u64;
		pub type DigestItem = runtime_primitives::generic::DigestItem<H256, u64>;
		pub type Digest = runtime_primitives::generic::Digest<DigestItem>;
		#[derive(Clone, PartialEq, Eq, Encode, Decode, Debug)]
		pub struct Extrinsic {}

		impl serde::Serialize for Extrinsic {
			fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
				unimplemented!()
			}
		}
		impl ExtrinsicT for Extrinsic {
			fn is_signed(&self) -> Option<bool> {
				unimplemented!()
			}
		}
		pub type Header = runtime_primitives::generic::Header<BlockNumber, BlakeTwo256, DigestItem>;
		pub type Block = runtime_primitives::generic::Block<Header, Extrinsic>;

		/// The declaration of the `Runtime` type and the implementation of the `GetNodeBlockType`
		/// trait are done by the `construct_runtime!` macro in a real runtime.
		struct Runtime {}
		impl GetNodeBlockType for Runtime {
			type NodeBlock = Block;
		}

		decl_runtime_apis! {
			pub trait Api {
				fn test(data: u64);
			}
		}

		impl_runtime_apis! {
			impl self::Api for Runtime {
				fn test(data: u64) {
					unimplemented!()
				}
			}
		}

		fn main() {}
	```
	*/
}

mod missing_path_for_trait {
	/*!
	```compile_fail
		#[macro_use]
		extern crate substrate_client;
		extern crate sr_primitives as runtime_primitives;
		extern crate substrate_primitives as primitives;
		#[macro_use]
		extern crate parity_codec_derive;
		extern crate serde;
		extern crate core;

		use primitives::hash::H256;
		use runtime_primitives::traits::{BlakeTwo256, GetNodeBlockType, Extrinsic as ExtrinsicT};

		// All the stuff we need to declare our `Block`
		pub type BlockNumber = u64;
		pub type DigestItem = runtime_primitives::generic::DigestItem<H256, u64>;
		pub type Digest = runtime_primitives::generic::Digest<DigestItem>;
		#[derive(Clone, PartialEq, Eq, Encode, Decode, Debug)]
		pub struct Extrinsic {}
		impl serde::Serialize for Extrinsic
		{
			fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
				unimplemented!()
			}
		}
		impl ExtrinsicT for Extrinsic {
			fn is_signed(&self) -> Option<bool> {
				unimplemented!()
			}
		}
		pub type Header = runtime_primitives::generic::Header<BlockNumber, BlakeTwo256, DigestItem>;
		pub type Block = runtime_primitives::generic::Block<Header, Extrinsic>;

		/// The declaration of the `Runtime` type and the implementation of the `GetNodeBlockType`
		/// trait are done by the `construct_runtime!` macro in a real runtime.
		struct Runtime {}
		impl GetNodeBlockType for Runtime {
			type NodeBlock = Block;
		}

		decl_runtime_apis! {
			pub trait Api {
				fn test(data: u64);
			}
		}

		impl_runtime_apis! {
			impl Api<Block> for Runtime {
				fn test(data: u64) {
					unimplemented!()
				}
			}
		}

		fn main() {}
	```
	*/
}

mod empty_impl_runtime_apis_call {
	/*!
	```compile_fail
		#[macro_use]
		extern crate substrate_client;
		extern crate sr_primitives as runtime_primitives;
		extern crate substrate_primitives as primitives;
		#[macro_use]
		extern crate parity_codec_derive;
		extern crate serde;
		extern crate core;

		use primitives::hash::H256;
		use runtime_primitives::traits::{BlakeTwo256, GetNodeBlockType, Extrinsic as ExtrinsicT};

		// All the stuff we need to declare our `Block`
		pub type BlockNumber = u64;
		pub type DigestItem = runtime_primitives::generic::DigestItem<H256, u64>;
		pub type Digest = runtime_primitives::generic::Digest<DigestItem>;
		#[derive(Clone, PartialEq, Eq, Encode, Decode, Debug)]
		pub struct Extrinsic {}
		impl serde::Serialize for Extrinsic
		{
			fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
				unimplemented!()
			}
		}
		impl ExtrinsicT for Extrinsic {
			fn is_signed(&self) -> Option<bool> {
				unimplemented!()
			}
		}
		pub type Header = runtime_primitives::generic::Header<BlockNumber, BlakeTwo256, DigestItem>;
		pub type Block = runtime_primitives::generic::Block<Header, Extrinsic>;

		/// The declaration of the `Runtime` type and the implementation of the `GetNodeBlockType`
		/// trait are done by the `construct_runtime!` macro in a real runtime.
		struct Runtime {}
		impl GetNodeBlockType for Runtime {
			type NodeBlock = Block;
		}

		decl_runtime_apis! {
			pub trait Api {
				fn test(data: u64);
			}
		}

		impl_runtime_apis! {}

		fn main() {}
	```
	*/
}

mod type_reference_in_impl_runtime_apis_call {
	/*!
	```compile_fail
		#[macro_use]
		extern crate substrate_client;
		extern crate sr_primitives as runtime_primitives;
		extern crate substrate_primitives as primitives;
		#[macro_use]
		extern crate parity_codec_derive;
		extern crate serde;
		extern crate core;

		use primitives::hash::H256;
		use runtime_primitives::traits::{BlakeTwo256, GetNodeBlockType, Extrinsic as ExtrinsicT};

		// All the stuff we need to declare our `Block`
		pub type BlockNumber = u64;
		pub type DigestItem = runtime_primitives::generic::DigestItem<H256, u64>;
		pub type Digest = runtime_primitives::generic::Digest<DigestItem>;
		#[derive(Clone, PartialEq, Eq, Encode, Decode, Debug)]
		pub struct Extrinsic {}
		impl serde::Serialize for Extrinsic
		{
			fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
				unimplemented!()
			}
		}
		impl ExtrinsicT for Extrinsic {
			fn is_signed(&self) -> Option<bool> {
				unimplemented!()
			}
		}
		pub type Header = runtime_primitives::generic::Header<BlockNumber, BlakeTwo256, DigestItem>;
		pub type Block = runtime_primitives::generic::Block<Header, Extrinsic>;

		/// The declaration of the `Runtime` type and the implementation of the `GetNodeBlockType`
		/// trait are done by the `construct_runtime!` macro in a real runtime.
		struct Runtime {}
		impl GetNodeBlockType for Runtime {
			type NodeBlock = Block;
		}

		decl_runtime_apis! {
			pub trait Api {
				fn test(data: u64);
			}
		}

		impl_runtime_apis! {
			impl self::Api<Block> for Runtime {
				fn test(data: &u64) {
					unimplemented!()
				}
			}
		}

		fn main() {}
	```
	*/
}

mod impl_incorrect_method_signature {
	/*!
	```compile_fail
		#[macro_use]
		extern crate substrate_client;
		extern crate sr_primitives as runtime_primitives;
		extern crate substrate_primitives as primitives;
		#[macro_use]
		extern crate parity_codec_derive;
		extern crate serde;
		extern crate core;

		use primitives::hash::H256;
		use runtime_primitives::traits::{BlakeTwo256, GetNodeBlockType, Extrinsic as ExtrinsicT};

		// All the stuff we need to declare our `Block`
		pub type BlockNumber = u64;
		pub type DigestItem = runtime_primitives::generic::DigestItem<H256, u64>;
		pub type Digest = runtime_primitives::generic::Digest<DigestItem>;
		#[derive(Clone, PartialEq, Eq, Encode, Decode, Debug)]
		pub struct Extrinsic {}
		impl serde::Serialize for Extrinsic
		{
			fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
				unimplemented!()
			}
		}
		impl ExtrinsicT for Extrinsic {
			fn is_signed(&self) -> Option<bool> {
				unimplemented!()
			}
		}
		pub type Header = runtime_primitives::generic::Header<BlockNumber, BlakeTwo256, DigestItem>;
		pub type Block = runtime_primitives::generic::Block<Header, Extrinsic>;

		/// The declaration of the `Runtime` type and the implementation of the `GetNodeBlockType`
		/// trait are done by the `construct_runtime!` macro in a real runtime.
		struct Runtime {}
		impl GetNodeBlockType for Runtime {
			type NodeBlock = Block;
		}

		decl_runtime_apis! {
			pub trait Api {
				fn test(data: u64);
			}
		}

		impl_runtime_apis! {
			impl self::Api<Block> for Runtime {
				fn test(data: String) {}
			}
		}

		fn main() {}
	```
	*/
}
