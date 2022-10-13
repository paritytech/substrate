use codec::{Decode, Encode, MaxEncodedLen};
use scale_info::TypeInfo;

/// A type describing our custom additional metadata stored in the orml-asset-registry.
#[derive(
	Clone,
	Copy,
	Default,
	PartialOrd,
	Ord,
	PartialEq,
	Eq,
	Debug,
	Encode,
	Decode,
	TypeInfo,
	MaxEncodedLen,
)]
pub struct CustomMetadata {
	/// XCM-related metadata, optional.
	pub xcm: Option<XcmMetadata>,
}

#[derive(
	Clone,
	Copy,
	Default,
	PartialOrd,
	Ord,
	PartialEq,
	Eq,
	Debug,
	Encode,
	Decode,
	TypeInfo,
	MaxEncodedLen,
)]
pub struct XcmMetadata {
	/// The fee charged for every second that an XCM message takes to execute.
	pub fee_per_second: u128,
}
