// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Primitives for the runtime modules.

use rstd::prelude::*;
use rstd;
#[cfg(not(feature = "std"))] use runtime_io;
use substrate_primitives;
use codec::Slicable;
pub use integer_sqrt::IntegerSquareRoot;
pub use num_traits::{Zero, One, Bounded};
use rstd::ops::{Add, Sub, Mul, Div, Rem, AddAssign, SubAssign, MulAssign, DivAssign, RemAssign};

/// Means of signature verification.
pub trait Verify {
	/// Type of the signer.
	type Signer;
	/// Verify a signature.
	fn verify(&self, msg: &[u8], signer: &Self::Signer) -> bool;
}

/// Simple payment making trait, operating on a single generic `AccountId` type.
pub trait MakePayment<AccountId> {
	/// Make some sort of payment concerning `who`.
	fn make_payment(who: &AccountId);
}

impl<T> MakePayment<T> for () {
	fn make_payment(_: &T) {}
}

/// Extensible conversion trait. Generic over both source and destination types.
pub trait Convert<A, B> {
	/// Make conversion.
	fn convert(a: A) -> B;
}

/// Simple trait similar to `Into`, except that it can be used to convert numerics between each
/// other.
pub trait As<T> {
	/// Convert forward (ala `Into::into`).
	fn as_(self) -> T;
	/// Convert backward (ala `From::from`).
	fn sa(T) -> Self;
}

macro_rules! impl_numerics {
	( $( $t:ty ),* ) => {
		$(
			impl_numerics!($t: u8, u16, u32, u64, usize, i8, i16, i32, i64, isize,);
		)*
	};
	( $f:ty : $t:ty, $( $rest:ty, )* ) => {
		impl As<$t> for $f {
			fn as_(self) -> $t { self as $t }
			fn sa(t: $t) -> Self { t as Self }
		}
		impl_numerics!($f: $( $rest, )*);
	};
	( $f:ty : ) => {}
}

impl_numerics!(u8, u16, u32, u64, usize, i8, i16, i32, i64, isize);

pub struct Identity;
impl<T> Convert<T, T> for Identity {
	fn convert(a: T) -> T { a }
}

pub trait MaybeEmpty {
	fn is_empty(&self) -> bool;
}

impl<T: Default + PartialEq> MaybeEmpty for T {
	fn is_empty(&self) -> bool {
		*self == T::default()
	}
}

pub trait HasPublicAux {
	type PublicAux: MaybeEmpty;
}

pub trait RefInto<T> {
	fn ref_into(&self) -> &T;
}
impl<T> RefInto<T> for T {
	fn ref_into(&self) -> &T { &self }
}

pub trait SimpleArithmetic:
	Zero + One + IntegerSquareRoot + As<usize> +
	Add<Self, Output = Self> + AddAssign<Self> +
	Sub<Self, Output = Self> + SubAssign<Self> +
	Mul<Self, Output = Self> + MulAssign<Self> +
	Div<Self, Output = Self> + DivAssign<Self> +
	Rem<Self, Output = Self> + RemAssign<Self> +
	PartialOrd<Self> + Ord
{}
impl<T:
	Zero + One + IntegerSquareRoot + As<usize> +
	Add<Self, Output = Self> + AddAssign<Self> +
	Sub<Self, Output = Self> + SubAssign<Self> +
	Mul<Self, Output = Self> + MulAssign<Self> +
	Div<Self, Output = Self> + DivAssign<Self> +
	Rem<Self, Output = Self> + RemAssign<Self> +
	PartialOrd<Self> + Ord
> SimpleArithmetic for T {}

pub trait SimpleBitOps:
	Sized +
	rstd::ops::BitOr<Self, Output = Self> +
	rstd::ops::BitAnd<Self, Output = Self>
{}
impl<T:
	Sized +
	rstd::ops::BitOr<Self, Output = Self> +
	rstd::ops::BitAnd<Self, Output = Self>
> SimpleBitOps for T {}

/// Something that can be executed.
pub trait Executable {
	fn execute();
}

impl Executable for () {
	fn execute() {}
}
impl<A: Executable, B: Executable> Executable for (A, B) {
	fn execute() {
		A::execute();
		B::execute();
	}
}

/// Something that acts like a `Digest` - it can have `Log`s `push`ed onto it and these `Log`s are
/// each `Slicable`.
pub trait Digest {
	type Item: Sized;
	fn push(&mut self, item: Self::Item);
}

impl Digest for substrate_primitives::Digest {
	type Item = substrate_primitives::block::Log;
	fn push(&mut self, item: Self::Item) {
		self.logs.push(item);
	}
}

/// Something which fulfills the abstract idea of a Substrate header. It has types for a `Number`,
/// a `Hash` and a `Digest`. It provides access to an `extrinsics_root`, `state_root` and
/// `parent_hash`, as well as a `digest` and a block `number`.
///
/// You can also create a `new` one from those fields.
pub trait Header: Sized + Slicable {
	type Number: Sized;
	type Hash: Sized;
	type Digest: Sized;
	fn number(&self) -> &Self::Number;
	fn extrinsics_root(&self) -> &Self::Hash;
	fn state_root(&self) -> &Self::Hash;
	fn parent_hash(&self) -> &Self::Hash;
	fn digest(&self) -> &Self::Digest;
	fn new(
		number: Self::Number,
		extrinsics_root: Self::Hash,
		state_root: Self::Hash,
		parent_hash: Self::Hash,
		digest: Self::Digest
	) -> Self;
}

impl Header for substrate_primitives::Header {
	type Number = substrate_primitives::block::Number;
	type Hash = substrate_primitives::block::HeaderHash;
	type Digest = substrate_primitives::block::Digest;
	fn number(&self) -> &Self::Number { &self.number }
	fn extrinsics_root(&self) -> &Self::Hash { &self.extrinsics_root }
	fn state_root(&self) -> &Self::Hash { &self.state_root }
	fn parent_hash(&self) -> &Self::Hash { &self.parent_hash }
	fn digest(&self) -> &Self::Digest { &self.digest }
	fn new(
		number: Self::Number,
		extrinsics_root: Self::Hash,
		state_root: Self::Hash,
		parent_hash: Self::Hash,
		digest: Self::Digest
	) -> Self {
		substrate_primitives::Header {
			number: number,
			extrinsics_root: extrinsics_root,
			state_root: state_root,
			parent_hash: parent_hash,
			digest: digest,
		}
	}
}

/// Something which fulfills the abstract idea of a Substrate block. It has types for an
/// `Extrinsic` piece of information as well as a `Header`.
///
/// You can get an iterator over each of the `extrinsics` and retrieve the `header`.
pub trait Block {
	type Extrinsic: Sized;
	type Header: Header;
	fn header(&self) -> &Self::Header;
	fn extrinsics(&self) -> &[Self::Extrinsic];
	fn deconstruct(self) -> (Self::Header, Vec<Self::Extrinsic>);
}

impl Block for substrate_primitives::Block {
	type Extrinsic = substrate_primitives::block::Extrinsic;
	type Header = substrate_primitives::Header;
	fn header(&self) -> &Self::Header {
		&self.header
	}
	fn extrinsics(&self) -> &[Self::Extrinsic] {
		&self.transactions[..]
	}
	fn deconstruct(self) -> (Self::Header, Vec<Self::Extrinsic>) {
		(self.header, self.transactions)
	}
}

/// A "checkable" piece of information, used by the standard Substrate Executive in order to
/// check the validity of a piece of extrinsic information, usually by verifying the signature.
pub trait Checkable: Sized {
	type Checked: Sized;
	fn check(self) -> Result<Self::Checked, Self>;
}

/// An "executable" piece of information, used by the standard Substrate Executive in order to
/// enact a piece of extrinsic information by marshalling and dispatching to a named functioon
/// call.
///
/// Also provides information on to whom this information is attributable and an index that allows
/// each piece of attributable information to be disambiguated.
pub trait Applyable {
	type AccountId;
	type Index;
	fn index(&self) -> &Self::Index;
	fn sender(&self) -> &Self::AccountId;
	fn apply(self);
}

/// Something that can be checked for equality and printed out to a debug channel if bad.
pub trait CheckEqual {
	fn check_equal(&self, other: &Self);
}

impl CheckEqual for substrate_primitives::H256 {
	#[cfg(feature = "std")]
	fn check_equal(&self, other: &Self) {
		use substrate_primitives::hexdisplay::HexDisplay;
		if &self.0 != &other.0 {
			println!("Hash: given={}, expected={}", HexDisplay::from(&self.0), HexDisplay::from(&other.0));
		}
	}

	#[cfg(not(feature = "std"))]
	fn check_equal(&self, other: &Self) {
		if self != other {
			runtime_io::print("Hash not equal");
			runtime_io::print(&self.0[..]);
			runtime_io::print(&other.0[..]);
		}
	}
}
