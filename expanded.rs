#![feature(prelude_import)]
#![no_std]
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

//! The Substrate runtime. This can be compiled with ``#[no_std]`, ready for Wasm.

// `construct_runtime!` does a lot of recursion and requires us to increase the limit to 256.
#![recursion_limit = "256"]
#[prelude_import]
use ::std::prelude::v1::*;
#[macro_use]
extern crate std as std;

#[macro_use]
extern crate runtime_primitives;

use rstd::prelude::*;
use parity_codec_derive::{Encode, Decode};
use substrate_metadata_derive::EncodeMetadata;
#[cfg(feature = "std")]
use support::{Serialize, Deserialize};
use support::construct_runtime;
use substrate_primitives::u32_trait::{_2, _4};
use node_primitives::{AccountId, AccountIndex, Balance, BlockNumber, Hash,
                      Index, SessionKey, Signature};
use grandpa::fg_primitives::{self, ScheduledChange};
use client::{block_builder::api::{self as block_builder_api, InherentData,
                                  CheckInherentsResult}, runtime_api as
             client_api, impl_runtime_apis};
use runtime_primitives::ApplyResult;
use runtime_primitives::transaction_validity::TransactionValidity;
use runtime_primitives::generic;
use runtime_primitives::traits::{Convert, BlakeTwo256, Block as BlockT,
                                 DigestFor, NumberFor, StaticLookup};
use version::RuntimeVersion;
use council::{motions as council_motions, voting as council_voting};
#[cfg(feature = "std")]
use council::seats as council_seats;
#[cfg(any(feature = "std", test))]
use version::NativeVersion;
use substrate_primitives::OpaqueMetadata;

#[cfg(any(feature = "std", test))]
pub use runtime_primitives::BuildStorage;
pub use consensus::Call as ConsensusCall;
pub use timestamp::Call as TimestampCall;
pub use balances::Call as BalancesCall;
pub use runtime_primitives::{Permill, Perbill};
pub use support::StorageValue;

/// Runtime version.
pub const VERSION: RuntimeVersion =
    RuntimeVersion{spec_name:






                       // the aura module handles offline-reports internally
                       // rather than using an explicit report system.




























                       { ::std::borrow::Cow::Borrowed("node") },
                   impl_name:
                       { ::std::borrow::Cow::Borrowed("substrate-node") },
                   authoring_version: 10,
                   spec_version: 28,
                   impl_version: 28,
                   apis: RUNTIME_API_VERSIONS,};
/// Native version.
#[cfg(any(feature = "std", test))]
pub fn native_version() -> NativeVersion {
    NativeVersion{runtime_version: VERSION,
                  can_author_with: Default::default(),}
}
impl system::Trait for Runtime {
    type
    Origin
    =
    Origin;
    type
    Index
    =
    Index;
    type
    BlockNumber
    =
    BlockNumber;
    type
    Hash
    =
    Hash;
    type
    Hashing
    =
    BlakeTwo256;
    type
    Digest
    =
    generic::Digest<Log>;
    type
    AccountId
    =
    AccountId;
    type
    Lookup
    =
    Indices;
    type
    Header
    =
    generic::Header<BlockNumber, BlakeTwo256, Log>;
    type
    Event
    =
    Event;
    type
    Log
    =
    Log;
}
impl aura::Trait for Runtime {
    type
    HandleReport
    =
    aura::StakingSlasher<Runtime>;
}
impl indices::Trait for Runtime {
    type
    AccountIndex
    =
    AccountIndex;
    type
    IsDeadAccount
    =
    Balances;
    type
    ResolveHint
    =
    indices::SimpleResolveHint<Self::AccountId, Self::AccountIndex>;
    type
    Event
    =
    Event;
}
impl balances::Trait for Runtime {
    type
    Balance
    =
    Balance;
    type
    OnFreeBalanceZero
    =
    ((Staking, Contract), Democracy);
    type
    OnNewAccount
    =
    Indices;
    type
    EnsureAccountLiquid
    =
    (Staking, Democracy);
    type
    Event
    =
    Event;
}
impl consensus::Trait for Runtime {
    type
    Log
    =
    Log;
    type
    SessionKey
    =
    SessionKey;
    type
    InherentOfflineReport
    =
    ();
}
impl timestamp::Trait for Runtime {
    type
    Moment
    =
    u64;
    type
    OnTimestampSet
    =
    Aura;
}
/// Session key conversion.
pub struct SessionKeyConversion;
impl Convert<AccountId, SessionKey> for SessionKeyConversion {
    fn convert(a: AccountId) -> SessionKey { a.to_fixed_bytes().into() }
}
impl session::Trait for Runtime {
    type
    ConvertAccountIdToSessionKey
    =
    SessionKeyConversion;
    type
    OnSessionChange
    =
    (Staking, grandpa::SyncedAuthorities<Runtime>);
    type
    Event
    =
    Event;
}
impl staking::Trait for Runtime {
    type
    Currency
    =
    balances::Module<Self>;
    type
    OnRewardMinted
    =
    Treasury;
    type
    Event
    =
    Event;
}
impl democracy::Trait for Runtime {
    type
    Currency
    =
    balances::Module<Self>;
    type
    Proposal
    =
    Call;
    type
    Event
    =
    Event;
}
impl council::Trait for Runtime {
    type
    Event
    =
    Event;
}
impl council::voting::Trait for Runtime {
    type
    Event
    =
    Event;
}
impl council::motions::Trait for Runtime {
    type
    Origin
    =
    Origin;
    type
    Proposal
    =
    Call;
    type
    Event
    =
    Event;
}
impl treasury::Trait for Runtime {
    type
    Currency
    =
    balances::Module<Self>;
    type
    ApproveOrigin
    =
    council_motions::EnsureMembers<_4>;
    type
    RejectOrigin
    =
    council_motions::EnsureMembers<_2>;
    type
    Event
    =
    Event;
}
impl contract::Trait for Runtime {
    type
    Call
    =
    Call;
    type
    Event
    =
    Event;
    type
    Gas
    =
    u64;
    type
    DetermineContractAddress
    =
    contract::SimpleAddressDeterminator<Runtime>;
    type
    ComputeDispatchFee
    =
    contract::DefaultDispatchFeeComputor<Runtime>;
}
impl sudo::Trait for Runtime {
    type
    Event
    =
    Event;
    type
    Proposal
    =
    Call;
}
impl grandpa::Trait for Runtime {
    type
    SessionKey
    =
    SessionKey;
    type
    Log
    =
    Log;
    type
    Event
    =
    Event;
}
#[structural_match]
#[rustc_copy_clone_marker]
pub struct Runtime;
#[automatically_derived]
#[allow(unused_qualifications)]
impl $crate::clone::Clone for Runtime {
    #[inline]
    fn clone(&self) -> Runtime { { *self } }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl $crate::marker::Copy for Runtime { }
#[automatically_derived]
#[allow(unused_qualifications)]
impl $crate::cmp::PartialEq for Runtime {
    #[inline]
    fn eq(&self, other: &Runtime) -> bool {
        match *other { Runtime => match *self { Runtime => true, }, }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl $crate::cmp::Eq for Runtime {
    #[inline]
    #[doc(hidden)]
    fn assert_receiver_is_total_eq(&self) -> () { { } }
}
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_ENCODEMETADATA_FOR_Runtime: () =
    {
        #[allow(unknown_lints)]
        #[allow(rust_2018_idioms)]
        extern crate substrate_metadata as _substrate_metadata;
        use _substrate_metadata::rstd::prelude::*;
        impl _substrate_metadata::EncodeMetadata for Runtime {
            fn type_name() -> _substrate_metadata::MetadataName {
                _substrate_metadata::MetadataName::Custom("node_runtime".into(),
                                                          "Runtime".into())
            }
            fn type_metadata_kind(registry:
                                      &mut _substrate_metadata::MetadataRegistry)
             -> _substrate_metadata::TypeMetadataKind {
                _substrate_metadata::TypeMetadataKind::Struct(<[_]>::into_vec(box
                                                                                  []))
            }
        }
    };
#[automatically_derived]
#[allow(unused_qualifications)]
impl $crate::fmt::Debug for Runtime {
    fn fmt(&self, f: &mut $crate::fmt::Formatter) -> $crate::fmt::Result {
        match *self {
            Runtime => {
                let mut debug_trait_builder = f.debug_tuple("Runtime");
                debug_trait_builder.finish()
            }
        }
    }
}
impl $crate::runtime_primitives::traits::GetNodeBlockType for Runtime {
    type
    NodeBlock
    =
    node_primitives::Block;
}
impl $crate::runtime_primitives::traits::GetRuntimeBlockType for Runtime {
    type
    RuntimeBlock
    =
    Block;
}
#[allow(non_camel_case_types)]
#[structural_match]
pub enum Event {
    system(system::Event),
    indices(indices::Event<Runtime>),
    balances(balances::Event<Runtime>),
    session(session::Event<Runtime>),
    staking(staking::Event<Runtime>),
    democracy(democracy::Event<Runtime>),
    council(council::Event<Runtime>),
    council_voting(council_voting::Event<Runtime>),
    council_motions(council_motions::Event<Runtime>),
    grandpa(grandpa::Event<Runtime>),
    treasury(treasury::Event<Runtime>),
    contract(contract::Event<Runtime>),
    sudo(sudo::Event<Runtime>),
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::clone::Clone for Event {
    #[inline]
    fn clone(&self) -> Event {
        match (&*self,) {
            (&Event::system(ref __self_0),) =>
            Event::system($crate::clone::Clone::clone(&(*__self_0))),
            (&Event::indices(ref __self_0),) =>
            Event::indices($crate::clone::Clone::clone(&(*__self_0))),
            (&Event::balances(ref __self_0),) =>
            Event::balances($crate::clone::Clone::clone(&(*__self_0))),
            (&Event::session(ref __self_0),) =>
            Event::session($crate::clone::Clone::clone(&(*__self_0))),
            (&Event::staking(ref __self_0),) =>
            Event::staking($crate::clone::Clone::clone(&(*__self_0))),
            (&Event::democracy(ref __self_0),) =>
            Event::democracy($crate::clone::Clone::clone(&(*__self_0))),
            (&Event::council(ref __self_0),) =>
            Event::council($crate::clone::Clone::clone(&(*__self_0))),
            (&Event::council_voting(ref __self_0),) =>
            Event::council_voting($crate::clone::Clone::clone(&(*__self_0))),
            (&Event::council_motions(ref __self_0),) =>
            Event::council_motions($crate::clone::Clone::clone(&(*__self_0))),
            (&Event::grandpa(ref __self_0),) =>
            Event::grandpa($crate::clone::Clone::clone(&(*__self_0))),
            (&Event::treasury(ref __self_0),) =>
            Event::treasury($crate::clone::Clone::clone(&(*__self_0))),
            (&Event::contract(ref __self_0),) =>
            Event::contract($crate::clone::Clone::clone(&(*__self_0))),
            (&Event::sudo(ref __self_0),) =>
            Event::sudo($crate::clone::Clone::clone(&(*__self_0))),
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::cmp::PartialEq for Event {
    #[inline]
    fn eq(&self, other: &Event) -> bool {
        {
            let __self_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*self) } as
                    isize;
            let __arg_1_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*other) } as
                    isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&Event::system(ref __self_0),
                     &Event::system(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Event::indices(ref __self_0),
                     &Event::indices(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Event::balances(ref __self_0),
                     &Event::balances(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Event::session(ref __self_0),
                     &Event::session(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Event::staking(ref __self_0),
                     &Event::staking(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Event::democracy(ref __self_0),
                     &Event::democracy(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Event::council(ref __self_0),
                     &Event::council(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Event::council_voting(ref __self_0),
                     &Event::council_voting(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Event::council_motions(ref __self_0),
                     &Event::council_motions(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Event::grandpa(ref __self_0),
                     &Event::grandpa(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Event::treasury(ref __self_0),
                     &Event::treasury(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Event::contract(ref __self_0),
                     &Event::contract(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Event::sudo(ref __self_0), &Event::sudo(ref __arg_1_0))
                    => (*__self_0) == (*__arg_1_0),
                    _ => unsafe { $crate::intrinsics::unreachable() }
                }
            } else { false }
        }
    }
    #[inline]
    fn ne(&self, other: &Event) -> bool {
        {
            let __self_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*self) } as
                    isize;
            let __arg_1_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*other) } as
                    isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&Event::system(ref __self_0),
                     &Event::system(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Event::indices(ref __self_0),
                     &Event::indices(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Event::balances(ref __self_0),
                     &Event::balances(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Event::session(ref __self_0),
                     &Event::session(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Event::staking(ref __self_0),
                     &Event::staking(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Event::democracy(ref __self_0),
                     &Event::democracy(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Event::council(ref __self_0),
                     &Event::council(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Event::council_voting(ref __self_0),
                     &Event::council_voting(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Event::council_motions(ref __self_0),
                     &Event::council_motions(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Event::grandpa(ref __self_0),
                     &Event::grandpa(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Event::treasury(ref __self_0),
                     &Event::treasury(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Event::contract(ref __self_0),
                     &Event::contract(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Event::sudo(ref __self_0), &Event::sudo(ref __arg_1_0))
                    => (*__self_0) != (*__arg_1_0),
                    _ => unsafe { $crate::intrinsics::unreachable() }
                }
            } else { true }
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::cmp::Eq for Event {
    #[inline]
    #[doc(hidden)]
    fn assert_receiver_is_total_eq(&self) -> () {
        {
            let _: $crate::cmp::AssertParamIsEq<system::Event>;
            let _: $crate::cmp::AssertParamIsEq<indices::Event<Runtime>>;
            let _: $crate::cmp::AssertParamIsEq<balances::Event<Runtime>>;
            let _: $crate::cmp::AssertParamIsEq<session::Event<Runtime>>;
            let _: $crate::cmp::AssertParamIsEq<staking::Event<Runtime>>;
            let _: $crate::cmp::AssertParamIsEq<democracy::Event<Runtime>>;
            let _: $crate::cmp::AssertParamIsEq<council::Event<Runtime>>;
            let _:
                    $crate::cmp::AssertParamIsEq<council_voting::Event<Runtime>>;
            let _:
                    $crate::cmp::AssertParamIsEq<council_motions::Event<Runtime>>;
            let _: $crate::cmp::AssertParamIsEq<grandpa::Event<Runtime>>;
            let _: $crate::cmp::AssertParamIsEq<treasury::Event<Runtime>>;
            let _: $crate::cmp::AssertParamIsEq<contract::Event<Runtime>>;
            let _: $crate::cmp::AssertParamIsEq<sudo::Event<Runtime>>;
        }
    }
}
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_ENCODE_FOR_Event: () =
    {
        #[allow(unknown_lints)]
        #[allow(rust_2018_idioms)]
        extern crate parity_codec as _parity_codec;
        impl _parity_codec::Encode for Event {
            fn encode_to<EncOut: _parity_codec::Output>(&self,
                                                        dest: &mut EncOut) {
                match *self {
                    Event::system(ref aa) => {
                        dest.push_byte(0usize as u8);
                        dest.push(aa);
                    }
                    Event::indices(ref aa) => {
                        dest.push_byte(1usize as u8);
                        dest.push(aa);
                    }
                    Event::balances(ref aa) => {
                        dest.push_byte(2usize as u8);
                        dest.push(aa);
                    }
                    Event::session(ref aa) => {
                        dest.push_byte(3usize as u8);
                        dest.push(aa);
                    }
                    Event::staking(ref aa) => {
                        dest.push_byte(4usize as u8);
                        dest.push(aa);
                    }
                    Event::democracy(ref aa) => {
                        dest.push_byte(5usize as u8);
                        dest.push(aa);
                    }
                    Event::council(ref aa) => {
                        dest.push_byte(6usize as u8);
                        dest.push(aa);
                    }
                    Event::council_voting(ref aa) => {
                        dest.push_byte(7usize as u8);
                        dest.push(aa);
                    }
                    Event::council_motions(ref aa) => {
                        dest.push_byte(8usize as u8);
                        dest.push(aa);
                    }
                    Event::grandpa(ref aa) => {
                        dest.push_byte(9usize as u8);
                        dest.push(aa);
                    }
                    Event::treasury(ref aa) => {
                        dest.push_byte(10usize as u8);
                        dest.push(aa);
                    }
                    Event::contract(ref aa) => {
                        dest.push_byte(11usize as u8);
                        dest.push(aa);
                    }
                    Event::sudo(ref aa) => {
                        dest.push_byte(12usize as u8);
                        dest.push(aa);
                    }
                }
            }
        }
    };
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_DECODE_FOR_Event: () =
    {
        #[allow(unknown_lints)]
        #[allow(rust_2018_idioms)]
        extern crate parity_codec as _parity_codec;
        impl _parity_codec::Decode for Event {
            fn decode<DecIn: _parity_codec::Input>(input: &mut DecIn)
             -> Option<Self> {
                match input.read_byte()? {
                    x if x == 0usize as u8 => {
                        Some(Event::system(_parity_codec::Decode::decode(input)?))
                    }
                    x if x == 1usize as u8 => {
                        Some(Event::indices(_parity_codec::Decode::decode(input)?))
                    }
                    x if x == 2usize as u8 => {
                        Some(Event::balances(_parity_codec::Decode::decode(input)?))
                    }
                    x if x == 3usize as u8 => {
                        Some(Event::session(_parity_codec::Decode::decode(input)?))
                    }
                    x if x == 4usize as u8 => {
                        Some(Event::staking(_parity_codec::Decode::decode(input)?))
                    }
                    x if x == 5usize as u8 => {
                        Some(Event::democracy(_parity_codec::Decode::decode(input)?))
                    }
                    x if x == 6usize as u8 => {
                        Some(Event::council(_parity_codec::Decode::decode(input)?))
                    }
                    x if x == 7usize as u8 => {
                        Some(Event::council_voting(_parity_codec::Decode::decode(input)?))
                    }
                    x if x == 8usize as u8 => {
                        Some(Event::council_motions(_parity_codec::Decode::decode(input)?))
                    }
                    x if x == 9usize as u8 => {
                        Some(Event::grandpa(_parity_codec::Decode::decode(input)?))
                    }
                    x if x == 10usize as u8 => {
                        Some(Event::treasury(_parity_codec::Decode::decode(input)?))
                    }
                    x if x == 11usize as u8 => {
                        Some(Event::contract(_parity_codec::Decode::decode(input)?))
                    }
                    x if x == 12usize as u8 => {
                        Some(Event::sudo(_parity_codec::Decode::decode(input)?))
                    }
                    _ => None,
                }
            }
        }
    };
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_ENCODEMETADATA_FOR_Event: () =
    {
        #[allow(unknown_lints)]
        #[allow(rust_2018_idioms)]
        extern crate substrate_metadata as _substrate_metadata;
        use _substrate_metadata::rstd::prelude::*;
        impl _substrate_metadata::EncodeMetadata for Event {
            fn type_name() -> _substrate_metadata::MetadataName {
                _substrate_metadata::MetadataName::Custom("node_runtime".into(),
                                                          "Event".into())
            }
            fn type_metadata_kind(registry:
                                      &mut _substrate_metadata::MetadataRegistry)
             -> _substrate_metadata::TypeMetadataKind {
                _substrate_metadata::TypeMetadataKind::Enum(<[_]>::into_vec(box
                                                                                [_substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "system".into(),
                                                                                                                          index:
                                                                                                                              0usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <system::Event
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <system::Event
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "indices".into(),
                                                                                                                          index:
                                                                                                                              1usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <indices::Event<Runtime>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <indices::Event<Runtime>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "balances".into(),
                                                                                                                          index:
                                                                                                                              2usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <balances::Event<Runtime>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <balances::Event<Runtime>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "session".into(),
                                                                                                                          index:
                                                                                                                              3usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <session::Event<Runtime>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <session::Event<Runtime>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "staking".into(),
                                                                                                                          index:
                                                                                                                              4usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <staking::Event<Runtime>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <staking::Event<Runtime>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "democracy".into(),
                                                                                                                          index:
                                                                                                                              5usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <democracy::Event<Runtime>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <democracy::Event<Runtime>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "council".into(),
                                                                                                                          index:
                                                                                                                              6usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <council::Event<Runtime>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <council::Event<Runtime>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "council_voting".into(),
                                                                                                                          index:
                                                                                                                              7usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <council_voting::Event<Runtime>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <council_voting::Event<Runtime>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "council_motions".into(),
                                                                                                                          index:
                                                                                                                              8usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <council_motions::Event<Runtime>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <council_motions::Event<Runtime>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "grandpa".into(),
                                                                                                                          index:
                                                                                                                              9usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <grandpa::Event<Runtime>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <grandpa::Event<Runtime>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "treasury".into(),
                                                                                                                          index:
                                                                                                                              10usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <treasury::Event<Runtime>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <treasury::Event<Runtime>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "contract".into(),
                                                                                                                          index:
                                                                                                                              11usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <contract::Event<Runtime>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <contract::Event<Runtime>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "sudo".into(),
                                                                                                                          index:
                                                                                                                              12usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <sudo::Event<Runtime>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <sudo::Event<Runtime>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),}]))
            }
        }
    };
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::fmt::Debug for Event {
    fn fmt(&self, f: &mut $crate::fmt::Formatter) -> $crate::fmt::Result {
        match (&*self,) {
            (&Event::system(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("system");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::indices(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("indices");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::balances(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("balances");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::session(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("session");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::staking(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("staking");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::democracy(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("democracy");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::council(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("council");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::council_voting(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("council_voting");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::council_motions(ref __self_0),) => {
                let mut debug_trait_builder =
                    f.debug_tuple("council_motions");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::grandpa(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("grandpa");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::treasury(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("treasury");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::contract(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("contract");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::sudo(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("sudo");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
        }
    }
}
impl From<system::Event> for Event {
    fn from(x: system::Event) -> Self { Event::system(x) }
}
impl From<indices::Event<Runtime>> for Event {
    fn from(x: indices::Event<Runtime>) -> Self { Event::indices(x) }
}
impl From<balances::Event<Runtime>> for Event {
    fn from(x: balances::Event<Runtime>) -> Self { Event::balances(x) }
}
impl From<session::Event<Runtime>> for Event {
    fn from(x: session::Event<Runtime>) -> Self { Event::session(x) }
}
impl From<staking::Event<Runtime>> for Event {
    fn from(x: staking::Event<Runtime>) -> Self { Event::staking(x) }
}
impl From<democracy::Event<Runtime>> for Event {
    fn from(x: democracy::Event<Runtime>) -> Self { Event::democracy(x) }
}
impl From<council::Event<Runtime>> for Event {
    fn from(x: council::Event<Runtime>) -> Self { Event::council(x) }
}
impl From<council_voting::Event<Runtime>> for Event {
    fn from(x: council_voting::Event<Runtime>) -> Self {
        Event::council_voting(x)
    }
}
impl From<council_motions::Event<Runtime>> for Event {
    fn from(x: council_motions::Event<Runtime>) -> Self {
        Event::council_motions(x)
    }
}
impl From<grandpa::Event<Runtime>> for Event {
    fn from(x: grandpa::Event<Runtime>) -> Self { Event::grandpa(x) }
}
impl From<treasury::Event<Runtime>> for Event {
    fn from(x: treasury::Event<Runtime>) -> Self { Event::treasury(x) }
}
impl From<contract::Event<Runtime>> for Event {
    fn from(x: contract::Event<Runtime>) -> Self { Event::contract(x) }
}
impl From<sudo::Event<Runtime>> for Event {
    fn from(x: sudo::Event<Runtime>) -> Self { Event::sudo(x) }
}
impl Runtime {
    #[allow(dead_code)]
    pub fn outer_event_metadata() -> $crate::event::OuterEventMetadata {
        $crate::event::OuterEventMetadata{name:
                                              $crate::event::DecodeDifferent::Encode("Event"),
                                          events:
                                              $crate::event::DecodeDifferent::Encode(&[("system",
                                                                                        $crate::event::FnEncode(system::Event::metadata)),
                                                                                       ("indices",
                                                                                        $crate::event::FnEncode(indices::Event::<Runtime>::metadata)),
                                                                                       ("balances",
                                                                                        $crate::event::FnEncode(balances::Event::<Runtime>::metadata)),
                                                                                       ("session",
                                                                                        $crate::event::FnEncode(session::Event::<Runtime>::metadata)),
                                                                                       ("staking",
                                                                                        $crate::event::FnEncode(staking::Event::<Runtime>::metadata)),
                                                                                       ("democracy",
                                                                                        $crate::event::FnEncode(democracy::Event::<Runtime>::metadata)),
                                                                                       ("council",
                                                                                        $crate::event::FnEncode(council::Event::<Runtime>::metadata)),
                                                                                       ("council_voting",
                                                                                        $crate::event::FnEncode(council_voting::Event::<Runtime>::metadata)),
                                                                                       ("council_motions",
                                                                                        $crate::event::FnEncode(council_motions::Event::<Runtime>::metadata)),
                                                                                       ("grandpa",
                                                                                        $crate::event::FnEncode(grandpa::Event::<Runtime>::metadata)),
                                                                                       ("treasury",
                                                                                        $crate::event::FnEncode(treasury::Event::<Runtime>::metadata)),
                                                                                       ("contract",
                                                                                        $crate::event::FnEncode(contract::Event::<Runtime>::metadata)),
                                                                                       ("sudo",
                                                                                        $crate::event::FnEncode(sudo::Event::<Runtime>::metadata))]),}
    }
    #[allow(dead_code)]
    pub fn __module_events_system()
     -> $crate::rstd::vec::Vec<$crate::event::EventMetadata> {
        system::Event::metadata()
    }
    pub fn __module_events_indices()
     -> $crate::rstd::vec::Vec<$crate::event::EventMetadata> {
        indices::Event::<Runtime>::metadata()
    }
    pub fn __module_events_balances()
     -> $crate::rstd::vec::Vec<$crate::event::EventMetadata> {
        balances::Event::<Runtime>::metadata()
    }
    pub fn __module_events_session()
     -> $crate::rstd::vec::Vec<$crate::event::EventMetadata> {
        session::Event::<Runtime>::metadata()
    }
    pub fn __module_events_staking()
     -> $crate::rstd::vec::Vec<$crate::event::EventMetadata> {
        staking::Event::<Runtime>::metadata()
    }
    pub fn __module_events_democracy()
     -> $crate::rstd::vec::Vec<$crate::event::EventMetadata> {
        democracy::Event::<Runtime>::metadata()
    }
    pub fn __module_events_council()
     -> $crate::rstd::vec::Vec<$crate::event::EventMetadata> {
        council::Event::<Runtime>::metadata()
    }
    pub fn __module_events_council_voting()
     -> $crate::rstd::vec::Vec<$crate::event::EventMetadata> {
        council_voting::Event::<Runtime>::metadata()
    }
    pub fn __module_events_council_motions()
     -> $crate::rstd::vec::Vec<$crate::event::EventMetadata> {
        council_motions::Event::<Runtime>::metadata()
    }
    pub fn __module_events_grandpa()
     -> $crate::rstd::vec::Vec<$crate::event::EventMetadata> {
        grandpa::Event::<Runtime>::metadata()
    }
    pub fn __module_events_treasury()
     -> $crate::rstd::vec::Vec<$crate::event::EventMetadata> {
        treasury::Event::<Runtime>::metadata()
    }
    pub fn __module_events_contract()
     -> $crate::rstd::vec::Vec<$crate::event::EventMetadata> {
        contract::Event::<Runtime>::metadata()
    }
    pub fn __module_events_sudo()
     -> $crate::rstd::vec::Vec<$crate::event::EventMetadata> {
        sudo::Event::<Runtime>::metadata()
    }
}
#[allow(non_camel_case_types)]
#[structural_match]
pub enum Origin {
    system(system::Origin<Runtime>),
    council_motions(council_motions::Origin),

    #[allow(dead_code)]
    Void($crate::Void),
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::clone::Clone for Origin {
    #[inline]
    fn clone(&self) -> Origin {
        match (&*self,) {
            (&Origin::system(ref __self_0),) =>
            Origin::system($crate::clone::Clone::clone(&(*__self_0))),
            (&Origin::council_motions(ref __self_0),) =>
            Origin::council_motions($crate::clone::Clone::clone(&(*__self_0))),
            (&Origin::Void(ref __self_0),) =>
            Origin::Void($crate::clone::Clone::clone(&(*__self_0))),
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::cmp::PartialEq for Origin {
    #[inline]
    fn eq(&self, other: &Origin) -> bool {
        {
            let __self_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*self) } as
                    isize;
            let __arg_1_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*other) } as
                    isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&Origin::system(ref __self_0),
                     &Origin::system(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Origin::council_motions(ref __self_0),
                     &Origin::council_motions(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Origin::Void(ref __self_0),
                     &Origin::Void(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    _ => unsafe { $crate::intrinsics::unreachable() }
                }
            } else { false }
        }
    }
    #[inline]
    fn ne(&self, other: &Origin) -> bool {
        {
            let __self_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*self) } as
                    isize;
            let __arg_1_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*other) } as
                    isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&Origin::system(ref __self_0),
                     &Origin::system(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Origin::council_motions(ref __self_0),
                     &Origin::council_motions(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Origin::Void(ref __self_0),
                     &Origin::Void(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    _ => unsafe { $crate::intrinsics::unreachable() }
                }
            } else { true }
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::cmp::Eq for Origin {
    #[inline]
    #[doc(hidden)]
    fn assert_receiver_is_total_eq(&self) -> () {
        {
            let _: $crate::cmp::AssertParamIsEq<system::Origin<Runtime>>;
            let _: $crate::cmp::AssertParamIsEq<council_motions::Origin>;
            let _: $crate::cmp::AssertParamIsEq<$crate::Void>;
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::fmt::Debug for Origin {
    fn fmt(&self, f: &mut $crate::fmt::Formatter) -> $crate::fmt::Result {
        match (&*self,) {
            (&Origin::system(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("system");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Origin::council_motions(ref __self_0),) => {
                let mut debug_trait_builder =
                    f.debug_tuple("council_motions");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Origin::Void(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Void");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
        }
    }
}
#[allow(dead_code)]
impl Origin {
    pub const
    INHERENT:
    Self
    =
    Origin::system(system::RawOrigin::Inherent);
    pub const
    ROOT:
    Self
    =
    Origin::system(system::RawOrigin::Root);
    pub fn signed(by: <Runtime as system::Trait>::AccountId) -> Self {
        Origin::system(system::RawOrigin::Signed(by))
    }
}
impl From<system::Origin<Runtime>> for Origin {
    fn from(x: system::Origin<Runtime>) -> Self { Origin::system(x) }
}
impl Into<Option<system::Origin<Runtime>>> for Origin {
    fn into(self) -> Option<system::Origin<Runtime>> {
        if let Origin::system(l) = self { Some(l) } else { None }
    }
}
impl From<Option<<Runtime as system::Trait>::AccountId>> for Origin {
    fn from(x: Option<<Runtime as system::Trait>::AccountId>) -> Self {
        <system::Origin<Runtime>>::from(x).into()
    }
}
impl From<council_motions::Origin> for Origin {
    fn from(x: council_motions::Origin) -> Self { Origin::council_motions(x) }
}
impl Into<Option<council_motions::Origin>> for Origin {
    fn into(self) -> Option<council_motions::Origin> {
        if let Origin::council_motions(l) = self { Some(l) } else { None }
    }
}
pub type System = system::Module<Runtime>;
pub type Aura = aura::Module<Runtime>;
pub type Timestamp = timestamp::Module<Runtime>;
pub type Consensus = consensus::Module<Runtime>;
pub type Indices = indices::Module<Runtime>;
pub type Balances = balances::Module<Runtime>;
pub type Session = session::Module<Runtime>;
pub type Staking = staking::Module<Runtime>;
pub type Democracy = democracy::Module<Runtime>;
pub type Council = council::Module<Runtime>;
pub type CouncilVoting = council_voting::Module<Runtime>;
pub type CouncilMotions = council_motions::Module<Runtime>;
pub type Grandpa = grandpa::Module<Runtime>;
pub type Treasury = treasury::Module<Runtime>;
pub type Contract = contract::Module<Runtime>;
pub type Sudo = sudo::Module<Runtime>;
type AllModules
    =
    (Aura, Timestamp, Consensus, Indices, Balances, Session, Staking,
     Democracy, Council, CouncilVoting, CouncilMotions, Grandpa, Treasury,
     Contract, Sudo);
#[structural_match]
pub enum Call {
    Timestamp(::srml_support::dispatch::CallableCallFor<Timestamp>),
    Consensus(::srml_support::dispatch::CallableCallFor<Consensus>),
    Indices(::srml_support::dispatch::CallableCallFor<Indices>),
    Balances(::srml_support::dispatch::CallableCallFor<Balances>),
    Session(::srml_support::dispatch::CallableCallFor<Session>),
    Staking(::srml_support::dispatch::CallableCallFor<Staking>),
    Democracy(::srml_support::dispatch::CallableCallFor<Democracy>),
    Council(::srml_support::dispatch::CallableCallFor<Council>),
    CouncilVoting(::srml_support::dispatch::CallableCallFor<CouncilVoting>),
    CouncilMotions(::srml_support::dispatch::CallableCallFor<CouncilMotions>),
    Grandpa(::srml_support::dispatch::CallableCallFor<Grandpa>),
    Treasury(::srml_support::dispatch::CallableCallFor<Treasury>),
    Contract(::srml_support::dispatch::CallableCallFor<Contract>),
    Sudo(::srml_support::dispatch::CallableCallFor<Sudo>),
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl $crate::clone::Clone for Call {
    #[inline]
    fn clone(&self) -> Call {
        match (&*self,) {
            (&Call::Timestamp(ref __self_0),) =>
            Call::Timestamp($crate::clone::Clone::clone(&(*__self_0))),
            (&Call::Consensus(ref __self_0),) =>
            Call::Consensus($crate::clone::Clone::clone(&(*__self_0))),
            (&Call::Indices(ref __self_0),) =>
            Call::Indices($crate::clone::Clone::clone(&(*__self_0))),
            (&Call::Balances(ref __self_0),) =>
            Call::Balances($crate::clone::Clone::clone(&(*__self_0))),
            (&Call::Session(ref __self_0),) =>
            Call::Session($crate::clone::Clone::clone(&(*__self_0))),
            (&Call::Staking(ref __self_0),) =>
            Call::Staking($crate::clone::Clone::clone(&(*__self_0))),
            (&Call::Democracy(ref __self_0),) =>
            Call::Democracy($crate::clone::Clone::clone(&(*__self_0))),
            (&Call::Council(ref __self_0),) =>
            Call::Council($crate::clone::Clone::clone(&(*__self_0))),
            (&Call::CouncilVoting(ref __self_0),) =>
            Call::CouncilVoting($crate::clone::Clone::clone(&(*__self_0))),
            (&Call::CouncilMotions(ref __self_0),) =>
            Call::CouncilMotions($crate::clone::Clone::clone(&(*__self_0))),
            (&Call::Grandpa(ref __self_0),) =>
            Call::Grandpa($crate::clone::Clone::clone(&(*__self_0))),
            (&Call::Treasury(ref __self_0),) =>
            Call::Treasury($crate::clone::Clone::clone(&(*__self_0))),
            (&Call::Contract(ref __self_0),) =>
            Call::Contract($crate::clone::Clone::clone(&(*__self_0))),
            (&Call::Sudo(ref __self_0),) =>
            Call::Sudo($crate::clone::Clone::clone(&(*__self_0))),
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl $crate::cmp::PartialEq for Call {
    #[inline]
    fn eq(&self, other: &Call) -> bool {
        {
            let __self_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*self) } as
                    isize;
            let __arg_1_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*other) } as
                    isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&Call::Timestamp(ref __self_0),
                     &Call::Timestamp(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::Consensus(ref __self_0),
                     &Call::Consensus(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::Indices(ref __self_0),
                     &Call::Indices(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::Balances(ref __self_0),
                     &Call::Balances(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::Session(ref __self_0),
                     &Call::Session(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::Staking(ref __self_0),
                     &Call::Staking(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::Democracy(ref __self_0),
                     &Call::Democracy(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::Council(ref __self_0),
                     &Call::Council(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::CouncilVoting(ref __self_0),
                     &Call::CouncilVoting(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::CouncilMotions(ref __self_0),
                     &Call::CouncilMotions(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::Grandpa(ref __self_0),
                     &Call::Grandpa(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::Treasury(ref __self_0),
                     &Call::Treasury(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::Contract(ref __self_0),
                     &Call::Contract(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::Sudo(ref __self_0), &Call::Sudo(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    _ => unsafe { $crate::intrinsics::unreachable() }
                }
            } else { false }
        }
    }
    #[inline]
    fn ne(&self, other: &Call) -> bool {
        {
            let __self_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*self) } as
                    isize;
            let __arg_1_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*other) } as
                    isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&Call::Timestamp(ref __self_0),
                     &Call::Timestamp(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::Consensus(ref __self_0),
                     &Call::Consensus(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::Indices(ref __self_0),
                     &Call::Indices(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::Balances(ref __self_0),
                     &Call::Balances(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::Session(ref __self_0),
                     &Call::Session(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::Staking(ref __self_0),
                     &Call::Staking(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::Democracy(ref __self_0),
                     &Call::Democracy(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::Council(ref __self_0),
                     &Call::Council(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::CouncilVoting(ref __self_0),
                     &Call::CouncilVoting(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::CouncilMotions(ref __self_0),
                     &Call::CouncilMotions(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::Grandpa(ref __self_0),
                     &Call::Grandpa(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::Treasury(ref __self_0),
                     &Call::Treasury(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::Contract(ref __self_0),
                     &Call::Contract(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::Sudo(ref __self_0), &Call::Sudo(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    _ => unsafe { $crate::intrinsics::unreachable() }
                }
            } else { true }
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl $crate::cmp::Eq for Call {
    #[inline]
    #[doc(hidden)]
    fn assert_receiver_is_total_eq(&self) -> () {
        {
            let _:
                    $crate::cmp::AssertParamIsEq<::srml_support::dispatch::CallableCallFor<Timestamp>>;
            let _:
                    $crate::cmp::AssertParamIsEq<::srml_support::dispatch::CallableCallFor<Consensus>>;
            let _:
                    $crate::cmp::AssertParamIsEq<::srml_support::dispatch::CallableCallFor<Indices>>;
            let _:
                    $crate::cmp::AssertParamIsEq<::srml_support::dispatch::CallableCallFor<Balances>>;
            let _:
                    $crate::cmp::AssertParamIsEq<::srml_support::dispatch::CallableCallFor<Session>>;
            let _:
                    $crate::cmp::AssertParamIsEq<::srml_support::dispatch::CallableCallFor<Staking>>;
            let _:
                    $crate::cmp::AssertParamIsEq<::srml_support::dispatch::CallableCallFor<Democracy>>;
            let _:
                    $crate::cmp::AssertParamIsEq<::srml_support::dispatch::CallableCallFor<Council>>;
            let _:
                    $crate::cmp::AssertParamIsEq<::srml_support::dispatch::CallableCallFor<CouncilVoting>>;
            let _:
                    $crate::cmp::AssertParamIsEq<::srml_support::dispatch::CallableCallFor<CouncilMotions>>;
            let _:
                    $crate::cmp::AssertParamIsEq<::srml_support::dispatch::CallableCallFor<Grandpa>>;
            let _:
                    $crate::cmp::AssertParamIsEq<::srml_support::dispatch::CallableCallFor<Treasury>>;
            let _:
                    $crate::cmp::AssertParamIsEq<::srml_support::dispatch::CallableCallFor<Contract>>;
            let _:
                    $crate::cmp::AssertParamIsEq<::srml_support::dispatch::CallableCallFor<Sudo>>;
        }
    }
}
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_ENCODEMETADATA_FOR_Call: () =
    {
        #[allow(unknown_lints)]
        #[allow(rust_2018_idioms)]
        extern crate substrate_metadata as _substrate_metadata;
        use _substrate_metadata::rstd::prelude::*;
        impl _substrate_metadata::EncodeMetadata for Call {
            fn type_name() -> _substrate_metadata::MetadataName {
                _substrate_metadata::MetadataName::Custom("node_runtime".into(),
                                                          "Call".into())
            }
            fn type_metadata_kind(registry:
                                      &mut _substrate_metadata::MetadataRegistry)
             -> _substrate_metadata::TypeMetadataKind {
                _substrate_metadata::TypeMetadataKind::Enum(<[_]>::into_vec(box
                                                                                [_substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "Timestamp".into(),
                                                                                                                          index:
                                                                                                                              0usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <::srml_support::dispatch::CallableCallFor<Timestamp>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <::srml_support::dispatch::CallableCallFor<Timestamp>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "Consensus".into(),
                                                                                                                          index:
                                                                                                                              1usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <::srml_support::dispatch::CallableCallFor<Consensus>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <::srml_support::dispatch::CallableCallFor<Consensus>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "Indices".into(),
                                                                                                                          index:
                                                                                                                              2usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <::srml_support::dispatch::CallableCallFor<Indices>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <::srml_support::dispatch::CallableCallFor<Indices>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "Balances".into(),
                                                                                                                          index:
                                                                                                                              3usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <::srml_support::dispatch::CallableCallFor<Balances>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <::srml_support::dispatch::CallableCallFor<Balances>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "Session".into(),
                                                                                                                          index:
                                                                                                                              4usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <::srml_support::dispatch::CallableCallFor<Session>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <::srml_support::dispatch::CallableCallFor<Session>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "Staking".into(),
                                                                                                                          index:
                                                                                                                              5usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <::srml_support::dispatch::CallableCallFor<Staking>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <::srml_support::dispatch::CallableCallFor<Staking>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "Democracy".into(),
                                                                                                                          index:
                                                                                                                              6usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <::srml_support::dispatch::CallableCallFor<Democracy>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <::srml_support::dispatch::CallableCallFor<Democracy>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "Council".into(),
                                                                                                                          index:
                                                                                                                              7usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <::srml_support::dispatch::CallableCallFor<Council>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <::srml_support::dispatch::CallableCallFor<Council>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "CouncilVoting".into(),
                                                                                                                          index:
                                                                                                                              8usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <::srml_support::dispatch::CallableCallFor<CouncilVoting>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <::srml_support::dispatch::CallableCallFor<CouncilVoting>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "CouncilMotions".into(),
                                                                                                                          index:
                                                                                                                              9usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <::srml_support::dispatch::CallableCallFor<CouncilMotions>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <::srml_support::dispatch::CallableCallFor<CouncilMotions>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "Grandpa".into(),
                                                                                                                          index:
                                                                                                                              10usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <::srml_support::dispatch::CallableCallFor<Grandpa>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <::srml_support::dispatch::CallableCallFor<Grandpa>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "Treasury".into(),
                                                                                                                          index:
                                                                                                                              11usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <::srml_support::dispatch::CallableCallFor<Treasury>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <::srml_support::dispatch::CallableCallFor<Treasury>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "Contract".into(),
                                                                                                                          index:
                                                                                                                              12usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <::srml_support::dispatch::CallableCallFor<Contract>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <::srml_support::dispatch::CallableCallFor<Contract>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "Sudo".into(),
                                                                                                                          index:
                                                                                                                              13usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <::srml_support::dispatch::CallableCallFor<Sudo>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <::srml_support::dispatch::CallableCallFor<Sudo>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),}]))
            }
        }
    };
#[automatically_derived]
#[allow(unused_qualifications)]
impl $crate::fmt::Debug for Call {
    fn fmt(&self, f: &mut $crate::fmt::Formatter) -> $crate::fmt::Result {
        match (&*self,) {
            (&Call::Timestamp(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Timestamp");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Consensus(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Consensus");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Indices(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Indices");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Balances(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Balances");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Session(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Session");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Staking(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Staking");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Democracy(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Democracy");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Council(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Council");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::CouncilVoting(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("CouncilVoting");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::CouncilMotions(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("CouncilMotions");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Grandpa(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Grandpa");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Treasury(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Treasury");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Contract(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Contract");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Sudo(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Sudo");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
        }
    }
}
impl $crate::dispatch::Decode for Call {
    fn decode<I: $crate::dispatch::Input>(input: &mut I) -> Option<Self> {
        let input_id = input.read_byte()?;
        {
            if input_id == (0) {
                let outer_dispatch_param =
                    $crate::dispatch::Decode::decode(input)?;
                return Some(Call::Timestamp(outer_dispatch_param));
            }
            {
                if input_id == (0 + 1) {
                    let outer_dispatch_param =
                        $crate::dispatch::Decode::decode(input)?;
                    return Some(Call::Consensus(outer_dispatch_param));
                }
                {
                    if input_id == (0 + 1 + 1) {
                        let outer_dispatch_param =
                            $crate::dispatch::Decode::decode(input)?;
                        return Some(Call::Indices(outer_dispatch_param));
                    }
                    {
                        if input_id == (0 + 1 + 1 + 1) {
                            let outer_dispatch_param =
                                $crate::dispatch::Decode::decode(input)?;
                            return Some(Call::Balances(outer_dispatch_param));
                        }
                        {
                            if input_id == (0 + 1 + 1 + 1 + 1) {
                                let outer_dispatch_param =
                                    $crate::dispatch::Decode::decode(input)?;
                                return Some(Call::Session(outer_dispatch_param));
                            }
                            {
                                if input_id == (0 + 1 + 1 + 1 + 1 + 1) {
                                    let outer_dispatch_param =
                                        $crate::dispatch::Decode::decode(input)?;
                                    return Some(Call::Staking(outer_dispatch_param));
                                }
                                {
                                    if input_id == (0 + 1 + 1 + 1 + 1 + 1 + 1)
                                       {
                                        let outer_dispatch_param =
                                            $crate::dispatch::Decode::decode(input)?;
                                        return Some(Call::Democracy(outer_dispatch_param));
                                    }
                                    {
                                        if input_id ==
                                               (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
                                           {
                                            let outer_dispatch_param =
                                                $crate::dispatch::Decode::decode(input)?;
                                            return Some(Call::Council(outer_dispatch_param));
                                        }
                                        {
                                            if input_id ==
                                                   (0 + 1 + 1 + 1 + 1 + 1 + 1
                                                        + 1 + 1) {
                                                let outer_dispatch_param =
                                                    $crate::dispatch::Decode::decode(input)?;
                                                return Some(Call::CouncilVoting(outer_dispatch_param));
                                            }
                                            {
                                                if input_id ==
                                                       (0 + 1 + 1 + 1 + 1 + 1
                                                            + 1 + 1 + 1 + 1) {
                                                    let outer_dispatch_param =
                                                        $crate::dispatch::Decode::decode(input)?;
                                                    return Some(Call::CouncilMotions(outer_dispatch_param));
                                                }
                                                {
                                                    if input_id ==
                                                           (0 + 1 + 1 + 1 + 1
                                                                + 1 + 1 + 1 +
                                                                1 + 1 + 1) {
                                                        let outer_dispatch_param =
                                                            $crate::dispatch::Decode::decode(input)?;
                                                        return Some(Call::Grandpa(outer_dispatch_param));
                                                    }
                                                    {
                                                        if input_id ==
                                                               (0 + 1 + 1 + 1
                                                                    + 1 + 1 +
                                                                    1 + 1 + 1
                                                                    + 1 + 1 +
                                                                    1) {
                                                            let outer_dispatch_param =
                                                                $crate::dispatch::Decode::decode(input)?;
                                                            return Some(Call::Treasury(outer_dispatch_param));
                                                        }
                                                        {
                                                            if input_id ==
                                                                   (0 + 1 + 1
                                                                        + 1 +
                                                                        1 + 1
                                                                        + 1 +
                                                                        1 + 1
                                                                        + 1 +
                                                                        1 + 1
                                                                        + 1) {
                                                                let outer_dispatch_param =
                                                                    $crate::dispatch::Decode::decode(input)?;
                                                                return Some(Call::Contract(outer_dispatch_param));
                                                            }
                                                            {
                                                                if input_id ==
                                                                       (0 + 1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1)
                                                                   {
                                                                    let outer_dispatch_param =
                                                                        $crate::dispatch::Decode::decode(input)?;
                                                                    return Some(Call::Sudo(outer_dispatch_param));
                                                                }
                                                                None
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
impl $crate::dispatch::Encode for Call {
    fn encode_to<W: $crate::dispatch::Output>(&self, dest: &mut W) {
        {
            if let Call::Timestamp(ref outer_dispatch_param) = *self {
                dest.push_byte((0) as u8);
                outer_dispatch_param.encode_to(dest);
            }
            {
                if let Call::Consensus(ref outer_dispatch_param) = *self {
                    dest.push_byte((0 + 1) as u8);
                    outer_dispatch_param.encode_to(dest);
                }
                {
                    if let Call::Indices(ref outer_dispatch_param) = *self {
                        dest.push_byte((0 + 1 + 1) as u8);
                        outer_dispatch_param.encode_to(dest);
                    }
                    {
                        if let Call::Balances(ref outer_dispatch_param) =
                               *self {
                            dest.push_byte((0 + 1 + 1 + 1) as u8);
                            outer_dispatch_param.encode_to(dest);
                        }
                        {
                            if let Call::Session(ref outer_dispatch_param) =
                                   *self {
                                dest.push_byte((0 + 1 + 1 + 1 + 1) as u8);
                                outer_dispatch_param.encode_to(dest);
                            }
                            {
                                if let Call::Staking(ref outer_dispatch_param)
                                       = *self {
                                    dest.push_byte((0 + 1 + 1 + 1 + 1 + 1) as
                                                       u8);
                                    outer_dispatch_param.encode_to(dest);
                                }
                                {
                                    if let Call::Democracy(ref outer_dispatch_param)
                                           = *self {
                                        dest.push_byte((0 + 1 + 1 + 1 + 1 + 1
                                                            + 1) as u8);
                                        outer_dispatch_param.encode_to(dest);
                                    }
                                    {
                                        if let Call::Council(ref outer_dispatch_param)
                                               = *self {
                                            dest.push_byte((0 + 1 + 1 + 1 + 1
                                                                + 1 + 1 + 1)
                                                               as u8);
                                            outer_dispatch_param.encode_to(dest);
                                        }
                                        {
                                            if let Call::CouncilVoting(ref outer_dispatch_param)
                                                   = *self {
                                                dest.push_byte((0 + 1 + 1 + 1
                                                                    + 1 + 1 +
                                                                    1 + 1 + 1)
                                                                   as u8);
                                                outer_dispatch_param.encode_to(dest);
                                            }
                                            {
                                                if let Call::CouncilMotions(ref outer_dispatch_param)
                                                       = *self {
                                                    dest.push_byte((0 + 1 + 1
                                                                        + 1 +
                                                                        1 + 1
                                                                        + 1 +
                                                                        1 + 1
                                                                        + 1)
                                                                       as u8);
                                                    outer_dispatch_param.encode_to(dest);
                                                }
                                                {
                                                    if let Call::Grandpa(ref outer_dispatch_param)
                                                           = *self {
                                                        dest.push_byte((0 + 1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1
                                                                            +
                                                                            1)
                                                                           as
                                                                           u8);
                                                        outer_dispatch_param.encode_to(dest);
                                                    }
                                                    {
                                                        if let Call::Treasury(ref outer_dispatch_param)
                                                               = *self {
                                                            dest.push_byte((0
                                                                                +
                                                                                1
                                                                                +
                                                                                1
                                                                                +
                                                                                1
                                                                                +
                                                                                1
                                                                                +
                                                                                1
                                                                                +
                                                                                1
                                                                                +
                                                                                1
                                                                                +
                                                                                1
                                                                                +
                                                                                1
                                                                                +
                                                                                1
                                                                                +
                                                                                1)
                                                                               as
                                                                               u8);
                                                            outer_dispatch_param.encode_to(dest);
                                                        }
                                                        {
                                                            if let Call::Contract(ref outer_dispatch_param)
                                                                   = *self {
                                                                dest.push_byte((0
                                                                                    +
                                                                                    1
                                                                                    +
                                                                                    1
                                                                                    +
                                                                                    1
                                                                                    +
                                                                                    1
                                                                                    +
                                                                                    1
                                                                                    +
                                                                                    1
                                                                                    +
                                                                                    1
                                                                                    +
                                                                                    1
                                                                                    +
                                                                                    1
                                                                                    +
                                                                                    1
                                                                                    +
                                                                                    1
                                                                                    +
                                                                                    1)
                                                                                   as
                                                                                   u8);
                                                                outer_dispatch_param.encode_to(dest);
                                                            }
                                                            {
                                                                if let Call::Sudo(ref outer_dispatch_param)
                                                                       = *self
                                                                       {
                                                                    dest.push_byte((0
                                                                                        +
                                                                                        1
                                                                                        +
                                                                                        1
                                                                                        +
                                                                                        1
                                                                                        +
                                                                                        1
                                                                                        +
                                                                                        1
                                                                                        +
                                                                                        1
                                                                                        +
                                                                                        1
                                                                                        +
                                                                                        1
                                                                                        +
                                                                                        1
                                                                                        +
                                                                                        1
                                                                                        +
                                                                                        1
                                                                                        +
                                                                                        1
                                                                                        +
                                                                                        1)
                                                                                       as
                                                                                       u8);
                                                                    outer_dispatch_param.encode_to(dest);
                                                                }
                                                                { }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
impl ::srml_support::dispatch::Dispatchable for Call {
    type
    Origin
    =
    Origin;
    type
    Trait
    =
    Call;
    fn dispatch(self, origin: Origin) -> ::srml_support::dispatch::Result {
        match self {
            Call::Timestamp(call) => call.dispatch(origin),
            Call::Consensus(call) => call.dispatch(origin),
            Call::Indices(call) => call.dispatch(origin),
            Call::Balances(call) => call.dispatch(origin),
            Call::Session(call) => call.dispatch(origin),
            Call::Staking(call) => call.dispatch(origin),
            Call::Democracy(call) => call.dispatch(origin),
            Call::Council(call) => call.dispatch(origin),
            Call::CouncilVoting(call) => call.dispatch(origin),
            Call::CouncilMotions(call) => call.dispatch(origin),
            Call::Grandpa(call) => call.dispatch(origin),
            Call::Treasury(call) => call.dispatch(origin),
            Call::Contract(call) => call.dispatch(origin),
            Call::Sudo(call) => call.dispatch(origin),
        }
    }
}
impl ::srml_support::dispatch::IsSubType<Timestamp> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Timestamp as ::srml_support::dispatch::Callable>::Call> {
        if let Call::Timestamp(ref r) = *self { Some(r) } else { None }
    }
}
impl ::srml_support::dispatch::IsSubType<Consensus> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Consensus as ::srml_support::dispatch::Callable>::Call> {
        if let Call::Consensus(ref r) = *self { Some(r) } else { None }
    }
}
impl ::srml_support::dispatch::IsSubType<Indices> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Indices as ::srml_support::dispatch::Callable>::Call> {
        if let Call::Indices(ref r) = *self { Some(r) } else { None }
    }
}
impl ::srml_support::dispatch::IsSubType<Balances> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Balances as ::srml_support::dispatch::Callable>::Call> {
        if let Call::Balances(ref r) = *self { Some(r) } else { None }
    }
}
impl ::srml_support::dispatch::IsSubType<Session> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Session as ::srml_support::dispatch::Callable>::Call> {
        if let Call::Session(ref r) = *self { Some(r) } else { None }
    }
}
impl ::srml_support::dispatch::IsSubType<Staking> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Staking as ::srml_support::dispatch::Callable>::Call> {
        if let Call::Staking(ref r) = *self { Some(r) } else { None }
    }
}
impl ::srml_support::dispatch::IsSubType<Democracy> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Democracy as ::srml_support::dispatch::Callable>::Call> {
        if let Call::Democracy(ref r) = *self { Some(r) } else { None }
    }
}
impl ::srml_support::dispatch::IsSubType<Council> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Council as ::srml_support::dispatch::Callable>::Call> {
        if let Call::Council(ref r) = *self { Some(r) } else { None }
    }
}
impl ::srml_support::dispatch::IsSubType<CouncilVoting> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<CouncilVoting as ::srml_support::dispatch::Callable>::Call> {
        if let Call::CouncilVoting(ref r) = *self { Some(r) } else { None }
    }
}
impl ::srml_support::dispatch::IsSubType<CouncilMotions> for Call {
    fn is_aux_sub_type(&self)
     ->
         Option<&<CouncilMotions as
                 ::srml_support::dispatch::Callable>::Call> {
        if let Call::CouncilMotions(ref r) = *self { Some(r) } else { None }
    }
}
impl ::srml_support::dispatch::IsSubType<Grandpa> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Grandpa as ::srml_support::dispatch::Callable>::Call> {
        if let Call::Grandpa(ref r) = *self { Some(r) } else { None }
    }
}
impl ::srml_support::dispatch::IsSubType<Treasury> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Treasury as ::srml_support::dispatch::Callable>::Call> {
        if let Call::Treasury(ref r) = *self { Some(r) } else { None }
    }
}
impl ::srml_support::dispatch::IsSubType<Contract> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Contract as ::srml_support::dispatch::Callable>::Call> {
        if let Call::Contract(ref r) = *self { Some(r) } else { None }
    }
}
impl ::srml_support::dispatch::IsSubType<Sudo> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Sudo as ::srml_support::dispatch::Callable>::Call> {
        if let Call::Sudo(ref r) = *self { Some(r) } else { None }
    }
}
impl Runtime {
    pub fn metadata() -> $crate::metadata::RuntimeMetadataPrefixed {
        let mut registry =
            $crate::substrate_metadata::MetadataRegistry::new();
        $crate::metadata::RuntimeMetadata::V2($crate::metadata::RuntimeMetadataV2{modules:
                                                                                      <[_]>::into_vec(box
                                                                                                          [$crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("system"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(system::Module::<Runtime>::store_metadata_name)),
                                                                                                                                            storage:
                                                                                                                                                {
                                                                                                                                                    system::Module::<Runtime>::store_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(system::Module::<Runtime>::store_metadata_functions)))
                                                                                                                                                },
                                                                                                                                            calls:
                                                                                                                                                None,
                                                                                                                                            event:
                                                                                                                                                Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode({
                                                                                                                                                                                                                              enum ProcMacroHack
                                                                                                                                                                                                                                   {
                                                                                                                                                                                                                                  Value
                                                                                                                                                                                                                                      =
                                                                                                                                                                                                                                      ("Runtime :: [ < __module_events_ system > ]",
                                                                                                                                                                                                                                       0).1,
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                              macro_rules! proc_macro_call((

                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                           =>
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           Runtime
                                                                                                                                                                                                                                                           ::
                                                                                                                                                                                                                                                           __module_events_system
                                                                                                                                                                                                                                                           }
                                                                                                                                                                                                                                                           });
                                                                                                                                                                                                                              {
                                                                                                                                                                                                                                  Runtime::__module_events_system
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                          }))),},
                                                                                                           $crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("aura"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(||
                                                                                                                                                                                                                         "")),
                                                                                                                                            storage:
                                                                                                                                                None,
                                                                                                                                            calls:
                                                                                                                                                None,
                                                                                                                                            event:
                                                                                                                                                None,},
                                                                                                           $crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("timestamp"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(timestamp::Module::<Runtime>::store_metadata_name)),
                                                                                                                                            storage:
                                                                                                                                                {
                                                                                                                                                    timestamp::Module::<Runtime>::store_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(timestamp::Module::<Runtime>::store_metadata_functions)))
                                                                                                                                                },
                                                                                                                                            calls:
                                                                                                                                                {
                                                                                                                                                    timestamp::Module::<Runtime>::call_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(timestamp::Module::<Runtime>::call_functions)))
                                                                                                                                                },
                                                                                                                                            event:
                                                                                                                                                None,},
                                                                                                           $crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("consensus"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(consensus::Module::<Runtime>::store_metadata_name)),
                                                                                                                                            storage:
                                                                                                                                                {
                                                                                                                                                    consensus::Module::<Runtime>::store_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(consensus::Module::<Runtime>::store_metadata_functions)))
                                                                                                                                                },
                                                                                                                                            calls:
                                                                                                                                                {
                                                                                                                                                    consensus::Module::<Runtime>::call_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(consensus::Module::<Runtime>::call_functions)))
                                                                                                                                                },
                                                                                                                                            event:
                                                                                                                                                None,},
                                                                                                           $crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("indices"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(indices::Module::<Runtime>::store_metadata_name)),
                                                                                                                                            storage:
                                                                                                                                                {
                                                                                                                                                    indices::Module::<Runtime>::store_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(indices::Module::<Runtime>::store_metadata_functions)))
                                                                                                                                                },
                                                                                                                                            calls:
                                                                                                                                                {
                                                                                                                                                    indices::Module::<Runtime>::call_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(indices::Module::<Runtime>::call_functions)))
                                                                                                                                                },
                                                                                                                                            event:
                                                                                                                                                Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode({
                                                                                                                                                                                                                              enum ProcMacroHack
                                                                                                                                                                                                                                   {
                                                                                                                                                                                                                                  Value
                                                                                                                                                                                                                                      =
                                                                                                                                                                                                                                      ("Runtime :: [ < __module_events_ indices > ]",
                                                                                                                                                                                                                                       0).1,
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                              macro_rules! proc_macro_call((

                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                           =>
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           Runtime
                                                                                                                                                                                                                                                           ::
                                                                                                                                                                                                                                                           __module_events_indices
                                                                                                                                                                                                                                                           }
                                                                                                                                                                                                                                                           });
                                                                                                                                                                                                                              {
                                                                                                                                                                                                                                  Runtime::__module_events_indices
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                          }))),},
                                                                                                           $crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("balances"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(balances::Module::<Runtime>::store_metadata_name)),
                                                                                                                                            storage:
                                                                                                                                                {
                                                                                                                                                    balances::Module::<Runtime>::store_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(balances::Module::<Runtime>::store_metadata_functions)))
                                                                                                                                                },
                                                                                                                                            calls:
                                                                                                                                                {
                                                                                                                                                    balances::Module::<Runtime>::call_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(balances::Module::<Runtime>::call_functions)))
                                                                                                                                                },
                                                                                                                                            event:
                                                                                                                                                Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode({
                                                                                                                                                                                                                              enum ProcMacroHack
                                                                                                                                                                                                                                   {
                                                                                                                                                                                                                                  Value
                                                                                                                                                                                                                                      =
                                                                                                                                                                                                                                      ("Runtime :: [ < __module_events_ balances > ]",
                                                                                                                                                                                                                                       0).1,
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                              macro_rules! proc_macro_call((

                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                           =>
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           Runtime
                                                                                                                                                                                                                                                           ::
                                                                                                                                                                                                                                                           __module_events_balances
                                                                                                                                                                                                                                                           }
                                                                                                                                                                                                                                                           });
                                                                                                                                                                                                                              {
                                                                                                                                                                                                                                  Runtime::__module_events_balances
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                          }))),},
                                                                                                           $crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("session"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(session::Module::<Runtime>::store_metadata_name)),
                                                                                                                                            storage:
                                                                                                                                                {
                                                                                                                                                    session::Module::<Runtime>::store_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(session::Module::<Runtime>::store_metadata_functions)))
                                                                                                                                                },
                                                                                                                                            calls:
                                                                                                                                                {
                                                                                                                                                    session::Module::<Runtime>::call_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(session::Module::<Runtime>::call_functions)))
                                                                                                                                                },
                                                                                                                                            event:
                                                                                                                                                Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode({
                                                                                                                                                                                                                              enum ProcMacroHack
                                                                                                                                                                                                                                   {
                                                                                                                                                                                                                                  Value
                                                                                                                                                                                                                                      =
                                                                                                                                                                                                                                      ("Runtime :: [ < __module_events_ session > ]",
                                                                                                                                                                                                                                       0).1,
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                              macro_rules! proc_macro_call((

                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                           =>
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           Runtime
                                                                                                                                                                                                                                                           ::
                                                                                                                                                                                                                                                           __module_events_session
                                                                                                                                                                                                                                                           }
                                                                                                                                                                                                                                                           });
                                                                                                                                                                                                                              {
                                                                                                                                                                                                                                  Runtime::__module_events_session
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                          }))),},
                                                                                                           $crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("staking"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(staking::Module::<Runtime>::store_metadata_name)),
                                                                                                                                            storage:
                                                                                                                                                {
                                                                                                                                                    staking::Module::<Runtime>::store_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(staking::Module::<Runtime>::store_metadata_functions)))
                                                                                                                                                },
                                                                                                                                            calls:
                                                                                                                                                {
                                                                                                                                                    staking::Module::<Runtime>::call_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(staking::Module::<Runtime>::call_functions)))
                                                                                                                                                },
                                                                                                                                            event:
                                                                                                                                                Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode({
                                                                                                                                                                                                                              enum ProcMacroHack
                                                                                                                                                                                                                                   {
                                                                                                                                                                                                                                  Value
                                                                                                                                                                                                                                      =
                                                                                                                                                                                                                                      ("Runtime :: [ < __module_events_ staking > ]",
                                                                                                                                                                                                                                       0).1,
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                              macro_rules! proc_macro_call((

                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                           =>
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           Runtime
                                                                                                                                                                                                                                                           ::
                                                                                                                                                                                                                                                           __module_events_staking
                                                                                                                                                                                                                                                           }
                                                                                                                                                                                                                                                           });
                                                                                                                                                                                                                              {
                                                                                                                                                                                                                                  Runtime::__module_events_staking
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                          }))),},
                                                                                                           $crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("democracy"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(democracy::Module::<Runtime>::store_metadata_name)),
                                                                                                                                            storage:
                                                                                                                                                {
                                                                                                                                                    democracy::Module::<Runtime>::store_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(democracy::Module::<Runtime>::store_metadata_functions)))
                                                                                                                                                },
                                                                                                                                            calls:
                                                                                                                                                {
                                                                                                                                                    democracy::Module::<Runtime>::call_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(democracy::Module::<Runtime>::call_functions)))
                                                                                                                                                },
                                                                                                                                            event:
                                                                                                                                                Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode({
                                                                                                                                                                                                                              enum ProcMacroHack
                                                                                                                                                                                                                                   {
                                                                                                                                                                                                                                  Value
                                                                                                                                                                                                                                      =
                                                                                                                                                                                                                                      ("Runtime :: [ < __module_events_ democracy > ]",
                                                                                                                                                                                                                                       0).1,
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                              macro_rules! proc_macro_call((

                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                           =>
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           Runtime
                                                                                                                                                                                                                                                           ::
                                                                                                                                                                                                                                                           __module_events_democracy
                                                                                                                                                                                                                                                           }
                                                                                                                                                                                                                                                           });
                                                                                                                                                                                                                              {
                                                                                                                                                                                                                                  Runtime::__module_events_democracy
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                          }))),},
                                                                                                           $crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("council"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(council::Module::<Runtime>::store_metadata_name)),
                                                                                                                                            storage:
                                                                                                                                                {
                                                                                                                                                    council::Module::<Runtime>::store_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(council::Module::<Runtime>::store_metadata_functions)))
                                                                                                                                                },
                                                                                                                                            calls:
                                                                                                                                                {
                                                                                                                                                    council::Module::<Runtime>::call_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(council::Module::<Runtime>::call_functions)))
                                                                                                                                                },
                                                                                                                                            event:
                                                                                                                                                Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode({
                                                                                                                                                                                                                              enum ProcMacroHack
                                                                                                                                                                                                                                   {
                                                                                                                                                                                                                                  Value
                                                                                                                                                                                                                                      =
                                                                                                                                                                                                                                      ("Runtime :: [ < __module_events_ council > ]",
                                                                                                                                                                                                                                       0).1,
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                              macro_rules! proc_macro_call((

                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                           =>
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           Runtime
                                                                                                                                                                                                                                                           ::
                                                                                                                                                                                                                                                           __module_events_council
                                                                                                                                                                                                                                                           }
                                                                                                                                                                                                                                                           });
                                                                                                                                                                                                                              {
                                                                                                                                                                                                                                  Runtime::__module_events_council
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                          }))),},
                                                                                                           $crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("council_voting"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(council_voting::Module::<Runtime>::store_metadata_name)),
                                                                                                                                            storage:
                                                                                                                                                {
                                                                                                                                                    council_voting::Module::<Runtime>::store_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(council_voting::Module::<Runtime>::store_metadata_functions)))
                                                                                                                                                },
                                                                                                                                            calls:
                                                                                                                                                {
                                                                                                                                                    council_voting::Module::<Runtime>::call_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(council_voting::Module::<Runtime>::call_functions)))
                                                                                                                                                },
                                                                                                                                            event:
                                                                                                                                                Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode({
                                                                                                                                                                                                                              enum ProcMacroHack
                                                                                                                                                                                                                                   {
                                                                                                                                                                                                                                  Value
                                                                                                                                                                                                                                      =
                                                                                                                                                                                                                                      ("Runtime :: [ < __module_events_ council_voting > ]",
                                                                                                                                                                                                                                       0).1,
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                              macro_rules! proc_macro_call((

                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                           =>
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           Runtime
                                                                                                                                                                                                                                                           ::
                                                                                                                                                                                                                                                           __module_events_council_voting
                                                                                                                                                                                                                                                           }
                                                                                                                                                                                                                                                           });
                                                                                                                                                                                                                              {
                                                                                                                                                                                                                                  Runtime::__module_events_council_voting
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                          }))),},
                                                                                                           $crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("council_motions"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(council_motions::Module::<Runtime>::store_metadata_name)),
                                                                                                                                            storage:
                                                                                                                                                {
                                                                                                                                                    council_motions::Module::<Runtime>::store_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(council_motions::Module::<Runtime>::store_metadata_functions)))
                                                                                                                                                },
                                                                                                                                            calls:
                                                                                                                                                {
                                                                                                                                                    council_motions::Module::<Runtime>::call_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(council_motions::Module::<Runtime>::call_functions)))
                                                                                                                                                },
                                                                                                                                            event:
                                                                                                                                                Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode({
                                                                                                                                                                                                                              enum ProcMacroHack
                                                                                                                                                                                                                                   {
                                                                                                                                                                                                                                  Value
                                                                                                                                                                                                                                      =
                                                                                                                                                                                                                                      ("Runtime :: [ < __module_events_ council_motions > ]",
                                                                                                                                                                                                                                       0).1,
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                              macro_rules! proc_macro_call((

                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                           =>
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           Runtime
                                                                                                                                                                                                                                                           ::
                                                                                                                                                                                                                                                           __module_events_council_motions
                                                                                                                                                                                                                                                           }
                                                                                                                                                                                                                                                           });
                                                                                                                                                                                                                              {
                                                                                                                                                                                                                                  Runtime::__module_events_council_motions
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                          }))),},
                                                                                                           $crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("grandpa"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(grandpa::Module::<Runtime>::store_metadata_name)),
                                                                                                                                            storage:
                                                                                                                                                {
                                                                                                                                                    grandpa::Module::<Runtime>::store_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(grandpa::Module::<Runtime>::store_metadata_functions)))
                                                                                                                                                },
                                                                                                                                            calls:
                                                                                                                                                {
                                                                                                                                                    grandpa::Module::<Runtime>::call_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(grandpa::Module::<Runtime>::call_functions)))
                                                                                                                                                },
                                                                                                                                            event:
                                                                                                                                                Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode({
                                                                                                                                                                                                                              enum ProcMacroHack
                                                                                                                                                                                                                                   {
                                                                                                                                                                                                                                  Value
                                                                                                                                                                                                                                      =
                                                                                                                                                                                                                                      ("Runtime :: [ < __module_events_ grandpa > ]",
                                                                                                                                                                                                                                       0).1,
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                              macro_rules! proc_macro_call((

                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                           =>
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           Runtime
                                                                                                                                                                                                                                                           ::
                                                                                                                                                                                                                                                           __module_events_grandpa
                                                                                                                                                                                                                                                           }
                                                                                                                                                                                                                                                           });
                                                                                                                                                                                                                              {
                                                                                                                                                                                                                                  Runtime::__module_events_grandpa
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                          }))),},
                                                                                                           $crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("treasury"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(treasury::Module::<Runtime>::store_metadata_name)),
                                                                                                                                            storage:
                                                                                                                                                {
                                                                                                                                                    treasury::Module::<Runtime>::store_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(treasury::Module::<Runtime>::store_metadata_functions)))
                                                                                                                                                },
                                                                                                                                            calls:
                                                                                                                                                {
                                                                                                                                                    treasury::Module::<Runtime>::call_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(treasury::Module::<Runtime>::call_functions)))
                                                                                                                                                },
                                                                                                                                            event:
                                                                                                                                                Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode({
                                                                                                                                                                                                                              enum ProcMacroHack
                                                                                                                                                                                                                                   {
                                                                                                                                                                                                                                  Value
                                                                                                                                                                                                                                      =
                                                                                                                                                                                                                                      ("Runtime :: [ < __module_events_ treasury > ]",
                                                                                                                                                                                                                                       0).1,
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                              macro_rules! proc_macro_call((

                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                           =>
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           Runtime
                                                                                                                                                                                                                                                           ::
                                                                                                                                                                                                                                                           __module_events_treasury
                                                                                                                                                                                                                                                           }
                                                                                                                                                                                                                                                           });
                                                                                                                                                                                                                              {
                                                                                                                                                                                                                                  Runtime::__module_events_treasury
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                          }))),},
                                                                                                           $crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("contract"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(contract::Module::<Runtime>::store_metadata_name)),
                                                                                                                                            storage:
                                                                                                                                                {
                                                                                                                                                    contract::Module::<Runtime>::store_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(contract::Module::<Runtime>::store_metadata_functions)))
                                                                                                                                                },
                                                                                                                                            calls:
                                                                                                                                                {
                                                                                                                                                    contract::Module::<Runtime>::call_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(contract::Module::<Runtime>::call_functions)))
                                                                                                                                                },
                                                                                                                                            event:
                                                                                                                                                Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode({
                                                                                                                                                                                                                              enum ProcMacroHack
                                                                                                                                                                                                                                   {
                                                                                                                                                                                                                                  Value
                                                                                                                                                                                                                                      =
                                                                                                                                                                                                                                      ("Runtime :: [ < __module_events_ contract > ]",
                                                                                                                                                                                                                                       0).1,
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                              macro_rules! proc_macro_call((

                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                           =>
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           Runtime
                                                                                                                                                                                                                                                           ::
                                                                                                                                                                                                                                                           __module_events_contract
                                                                                                                                                                                                                                                           }
                                                                                                                                                                                                                                                           });
                                                                                                                                                                                                                              {
                                                                                                                                                                                                                                  Runtime::__module_events_contract
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                          }))),},
                                                                                                           $crate::metadata::ModuleMetadata{name:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode("sudo"),
                                                                                                                                            prefix:
                                                                                                                                                $crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(sudo::Module::<Runtime>::store_metadata_name)),
                                                                                                                                            storage:
                                                                                                                                                {
                                                                                                                                                    sudo::Module::<Runtime>::store_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(sudo::Module::<Runtime>::store_metadata_functions)))
                                                                                                                                                },
                                                                                                                                            calls:
                                                                                                                                                {
                                                                                                                                                    sudo::Module::<Runtime>::call_metadata_register(&mut registry);
                                                                                                                                                    Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode(sudo::Module::<Runtime>::call_functions)))
                                                                                                                                                },
                                                                                                                                            event:
                                                                                                                                                Some($crate::metadata::DecodeDifferent::Encode($crate::metadata::FnEncode({
                                                                                                                                                                                                                              enum ProcMacroHack
                                                                                                                                                                                                                                   {
                                                                                                                                                                                                                                  Value
                                                                                                                                                                                                                                      =
                                                                                                                                                                                                                                      ("Runtime :: [ < __module_events_ sudo > ]",
                                                                                                                                                                                                                                       0).1,
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                              macro_rules! proc_macro_call((

                                                                                                                                                                                                                                                           )
                                                                                                                                                                                                                                                           =>
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           {
                                                                                                                                                                                                                                                           Runtime
                                                                                                                                                                                                                                                           ::
                                                                                                                                                                                                                                                           __module_events_sudo
                                                                                                                                                                                                                                                           }
                                                                                                                                                                                                                                                           });
                                                                                                                                                                                                                              {
                                                                                                                                                                                                                                  Runtime::__module_events_sudo
                                                                                                                                                                                                                              }
                                                                                                                                                                                                                          }))),}]),
                                                                                  type_registry:
                                                                                      registry,}).into()
    }
}
/// Wrapper for all possible log entries for the `$trait` runtime. Provides binary-compatible
/// `Encode`/`Decode` implementations with the corresponding `generic::DigestItem`.
#[allow(non_camel_case_types)]
#[structural_match]
pub struct Log(InternalLog);
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::clone::Clone for Log {
    #[inline]
    fn clone(&self) -> Log {
        match *self {
            Log(ref __self_0_0) =>
            Log($crate::clone::Clone::clone(&(*__self_0_0))),
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::cmp::PartialEq for Log {
    #[inline]
    fn eq(&self, other: &Log) -> bool {
        match *other {
            Log(ref __self_1_0) =>
            match *self {
                Log(ref __self_0_0) => (*__self_0_0) == (*__self_1_0),
            },
        }
    }
    #[inline]
    fn ne(&self, other: &Log) -> bool {
        match *other {
            Log(ref __self_1_0) =>
            match *self {
                Log(ref __self_0_0) => (*__self_0_0) != (*__self_1_0),
            },
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::cmp::Eq for Log {
    #[inline]
    #[doc(hidden)]
    fn assert_receiver_is_total_eq(&self) -> () {
        { let _: $crate::cmp::AssertParamIsEq<InternalLog>; }
    }
}
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_ENCODEMETADATA_FOR_Log: () =
    {
        #[allow(unknown_lints)]
        #[allow(rust_2018_idioms)]
        extern crate substrate_metadata as _substrate_metadata;
        use _substrate_metadata::rstd::prelude::*;
        impl _substrate_metadata::EncodeMetadata for Log {
            fn type_name() -> _substrate_metadata::MetadataName {
                _substrate_metadata::MetadataName::Custom("node_runtime".into(),
                                                          "Log".into())
            }
            fn type_metadata_kind(registry:
                                      &mut _substrate_metadata::MetadataRegistry)
             -> _substrate_metadata::TypeMetadataKind {
                _substrate_metadata::TypeMetadataKind::Struct(<[_]>::into_vec(box
                                                                                  [{
                                                                                       let type_name =
                                                                                           <InternalLog
                                                                                               as
                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                       registry.register(type_name.clone(),
                                                                                                         <InternalLog
                                                                                                             as
                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                          as
                                                                                                                                                                          u16),
                                                                                                                          ty:
                                                                                                                              type_name,}
                                                                                   }]))
            }
        }
    };
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::fmt::Debug for Log {
    fn fmt(&self, f: &mut $crate::fmt::Formatter) -> $crate::fmt::Result {
        match *self {
            Log(ref __self_0_0) => {
                let mut debug_trait_builder = f.debug_tuple("Log");
                let _ = debug_trait_builder.field(&&(*__self_0_0));
                debug_trait_builder.finish()
            }
        }
    }
}
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_SERIALIZE_FOR_Log: () =
    {
        #[allow(unknown_lints)]
        #[allow(rust_2018_idioms)]
        extern crate serde as _serde;
        #[allow(unused_macros)]
        macro_rules! try(( $ __expr : expr ) => {
                         match $ __expr {
                         _serde :: export :: Ok ( __val ) => __val , _serde ::
                         export :: Err ( __err ) => {
                         return _serde :: export :: Err ( __err ) ; } } });
        #[automatically_derived]
        impl _serde::Serialize for Log {
            fn serialize<__S>(&self, __serializer: __S)
             -> _serde::export::Result<__S::Ok, __S::Error> where
             __S: _serde::Serializer {
                _serde::Serializer::serialize_newtype_struct(__serializer,
                                                             "Log", &self.0)
            }
        }
    };
/// All possible log entries for the `$trait` runtime. `Encode`/`Decode` implementations
/// are auto-generated => it is not binary-compatible with `generic::DigestItem`.
#[allow(non_camel_case_types)]
#[structural_match]
pub enum InternalLog {
    system(system::Log<Runtime>),
    consensus(consensus::Log<Runtime>),
    grandpa(grandpa::Log<Runtime>),
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::clone::Clone for InternalLog {
    #[inline]
    fn clone(&self) -> InternalLog {
        match (&*self,) {
            (&InternalLog::system(ref __self_0),) =>
            InternalLog::system($crate::clone::Clone::clone(&(*__self_0))),
            (&InternalLog::consensus(ref __self_0),) =>
            InternalLog::consensus($crate::clone::Clone::clone(&(*__self_0))),
            (&InternalLog::grandpa(ref __self_0),) =>
            InternalLog::grandpa($crate::clone::Clone::clone(&(*__self_0))),
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::cmp::PartialEq for InternalLog {
    #[inline]
    fn eq(&self, other: &InternalLog) -> bool {
        {
            let __self_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*self) } as
                    isize;
            let __arg_1_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*other) } as
                    isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&InternalLog::system(ref __self_0),
                     &InternalLog::system(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&InternalLog::consensus(ref __self_0),
                     &InternalLog::consensus(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&InternalLog::grandpa(ref __self_0),
                     &InternalLog::grandpa(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    _ => unsafe { $crate::intrinsics::unreachable() }
                }
            } else { false }
        }
    }
    #[inline]
    fn ne(&self, other: &InternalLog) -> bool {
        {
            let __self_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*self) } as
                    isize;
            let __arg_1_vi =
                unsafe { $crate::intrinsics::discriminant_value(&*other) } as
                    isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&InternalLog::system(ref __self_0),
                     &InternalLog::system(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&InternalLog::consensus(ref __self_0),
                     &InternalLog::consensus(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&InternalLog::grandpa(ref __self_0),
                     &InternalLog::grandpa(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    _ => unsafe { $crate::intrinsics::unreachable() }
                }
            } else { true }
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::cmp::Eq for InternalLog {
    #[inline]
    #[doc(hidden)]
    fn assert_receiver_is_total_eq(&self) -> () {
        {
            let _: $crate::cmp::AssertParamIsEq<system::Log<Runtime>>;
            let _: $crate::cmp::AssertParamIsEq<consensus::Log<Runtime>>;
            let _: $crate::cmp::AssertParamIsEq<grandpa::Log<Runtime>>;
        }
    }
}
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_ENCODE_FOR_InternalLog: () =
    {
        #[allow(unknown_lints)]
        #[allow(rust_2018_idioms)]
        extern crate parity_codec as _parity_codec;
        impl _parity_codec::Encode for InternalLog {
            fn encode_to<EncOut: _parity_codec::Output>(&self,
                                                        dest: &mut EncOut) {
                match *self {
                    InternalLog::system(ref aa) => {
                        dest.push_byte(0usize as u8);
                        dest.push(aa);
                    }
                    InternalLog::consensus(ref aa) => {
                        dest.push_byte(1usize as u8);
                        dest.push(aa);
                    }
                    InternalLog::grandpa(ref aa) => {
                        dest.push_byte(2usize as u8);
                        dest.push(aa);
                    }
                }
            }
        }
    };
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_DECODE_FOR_InternalLog: () =
    {
        #[allow(unknown_lints)]
        #[allow(rust_2018_idioms)]
        extern crate parity_codec as _parity_codec;
        impl _parity_codec::Decode for InternalLog {
            fn decode<DecIn: _parity_codec::Input>(input: &mut DecIn)
             -> Option<Self> {
                match input.read_byte()? {
                    x if x == 0usize as u8 => {
                        Some(InternalLog::system(_parity_codec::Decode::decode(input)?))
                    }
                    x if x == 1usize as u8 => {
                        Some(InternalLog::consensus(_parity_codec::Decode::decode(input)?))
                    }
                    x if x == 2usize as u8 => {
                        Some(InternalLog::grandpa(_parity_codec::Decode::decode(input)?))
                    }
                    _ => None,
                }
            }
        }
    };
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_ENCODEMETADATA_FOR_InternalLog: () =
    {
        #[allow(unknown_lints)]
        #[allow(rust_2018_idioms)]
        extern crate substrate_metadata as _substrate_metadata;
        use _substrate_metadata::rstd::prelude::*;
        impl _substrate_metadata::EncodeMetadata for InternalLog {
            fn type_name() -> _substrate_metadata::MetadataName {
                _substrate_metadata::MetadataName::Custom("node_runtime".into(),
                                                          "InternalLog".into())
            }
            fn type_metadata_kind(registry:
                                      &mut _substrate_metadata::MetadataRegistry)
             -> _substrate_metadata::TypeMetadataKind {
                _substrate_metadata::TypeMetadataKind::Enum(<[_]>::into_vec(box
                                                                                [_substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "system".into(),
                                                                                                                          index:
                                                                                                                              0usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <system::Log<Runtime>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <system::Log<Runtime>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "consensus".into(),
                                                                                                                          index:
                                                                                                                              1usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <consensus::Log<Runtime>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <consensus::Log<Runtime>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),},
                                                                                 _substrate_metadata::EnumVariantMetadata{name:
                                                                                                                              "grandpa".into(),
                                                                                                                          index:
                                                                                                                              2usize
                                                                                                                                  as
                                                                                                                                  u16,
                                                                                                                          fields:
                                                                                                                              <[_]>::into_vec(box
                                                                                                                                                  [{
                                                                                                                                                       let type_name =
                                                                                                                                                           <grandpa::Log<Runtime>
                                                                                                                                                               as
                                                                                                                                                               _substrate_metadata::EncodeMetadata>::type_name();
                                                                                                                                                       registry.register(type_name.clone(),
                                                                                                                                                                         <grandpa::Log<Runtime>
                                                                                                                                                                             as
                                                                                                                                                                             _substrate_metadata::EncodeMetadata>::type_metadata_kind);
                                                                                                                                                       _substrate_metadata::FieldMetadata{name:
                                                                                                                                                                                              _substrate_metadata::FieldName::Unnamed(0usize
                                                                                                                                                                                                                                          as
                                                                                                                                                                                                                                          u16),
                                                                                                                                                                                          ty:
                                                                                                                                                                                              type_name,}
                                                                                                                                                   }]),}]))
            }
        }
    };
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl $crate::fmt::Debug for InternalLog {
    fn fmt(&self, f: &mut $crate::fmt::Formatter) -> $crate::fmt::Result {
        match (&*self,) {
            (&InternalLog::system(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("system");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&InternalLog::consensus(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("consensus");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&InternalLog::grandpa(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("grandpa");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
        }
    }
}
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_SERIALIZE_FOR_InternalLog: () =
    {
        #[allow(unknown_lints)]
        #[allow(rust_2018_idioms)]
        extern crate serde as _serde;
        #[allow(unused_macros)]
        macro_rules! try(( $ __expr : expr ) => {
                         match $ __expr {
                         _serde :: export :: Ok ( __val ) => __val , _serde ::
                         export :: Err ( __err ) => {
                         return _serde :: export :: Err ( __err ) ; } } });
        #[automatically_derived]
        impl _serde::Serialize for InternalLog {
            fn serialize<__S>(&self, __serializer: __S)
             -> _serde::export::Result<__S::Ok, __S::Error> where
             __S: _serde::Serializer {
                match *self {
                    InternalLog::system(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "InternalLog",
                                                                  0u32,
                                                                  "system",
                                                                  __field0),
                    InternalLog::consensus(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "InternalLog",
                                                                  1u32,
                                                                  "consensus",
                                                                  __field0),
                    InternalLog::grandpa(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "InternalLog",
                                                                  2u32,
                                                                  "grandpa",
                                                                  __field0),
                }
            }
        }
    };
impl Log {
    /// Try to convert `$name` into `generic::DigestItemRef`. Returns Some when
    /// `self` is a 'system' log && it has been marked as 'system' in macro call.
    /// Otherwise, None is returned.
    #[allow(unreachable_patterns)]
    fn dref<'a>(&'a self)
     -> Option<$crate::generic::DigestItemRef<'a, Hash, SessionKey>> {
        match self.0 {
            InternalLog::system(system::RawLog::ChangesTrieRoot(ref v)) =>
            Some($crate::generic::DigestItemRef::ChangesTrieRoot(v)),
            InternalLog::consensus(consensus::RawLog::AuthoritiesChange(ref v))
            => Some($crate::generic::DigestItemRef::AuthoritiesChange(v)),
            _ => None,
        }
    }
}
impl $crate::traits::DigestItem for Log {
    type
    Hash
    =
    <$crate::generic::DigestItem<Hash, SessionKey> as
    $crate::traits::DigestItem>::Hash;
    type
    AuthorityId
    =
    <$crate::generic::DigestItem<Hash, SessionKey> as
    $crate::traits::DigestItem>::AuthorityId;
    fn as_authorities_change(&self) -> Option<&[Self::AuthorityId]> {
        self.dref().and_then(|dref| dref.as_authorities_change())
    }
    fn as_changes_trie_root(&self) -> Option<&Self::Hash> {
        self.dref().and_then(|dref| dref.as_changes_trie_root())
    }
}
impl From<$crate::generic::DigestItem<Hash, SessionKey>> for Log {
    /// Converts `generic::DigestItem` into `$name`. If `generic::DigestItem` represents
    /// a system item which is supported by the runtime, it is returned.
    /// Otherwise we expect a `Other` log item. Trying to convert from anything other
    /// will lead to panic in runtime, since the runtime does not supports this 'system'
    /// log item.
    #[allow(unreachable_patterns)]
    fn from(gen: $crate::generic::DigestItem<Hash, SessionKey>) -> Self {
        match gen {
            $crate::generic::DigestItem::ChangesTrieRoot(value) =>
            Log(InternalLog::system(system::RawLog::ChangesTrieRoot(value))),
            $crate::generic::DigestItem::AuthoritiesChange(value) =>
            Log(InternalLog::consensus(consensus::RawLog::AuthoritiesChange(value))),
            _ =>
            gen.as_other().and_then(|value|
                                        $crate::codec::Decode::decode(&mut &value[..])).map(Log).expect("not allowed to fail in runtime"),
        }
    }
}
impl $crate::codec::Decode for Log {
    /// `generic::DigestItem` binray compatible decode.
    fn decode<I: $crate::codec::Input>(input: &mut I) -> Option<Self> {
        let gen: $crate::generic::DigestItem<Hash, SessionKey> =
            $crate::codec::Decode::decode(input)?;
        Some(Log::from(gen))
    }
}
impl $crate::codec::Encode for Log {
    /// `generic::DigestItem` binray compatible encode.
    fn encode(&self) -> Vec<u8> {
        match self.dref() {
            Some(dref) => dref.encode(),
            None => {
                let gen: $crate::generic::DigestItem<Hash, SessionKey> =
                    $crate::generic::DigestItem::Other(self.0.encode());
                gen.encode()
            }
        }
    }
}
impl From<system::Log<Runtime>> for Log {
    /// Converts single module log item into `$name`.
    fn from(x: system::Log<Runtime>) -> Self { Log(x.into()) }
}
impl From<system::Log<Runtime>> for InternalLog {
    /// Converts single module log item into `$internal`.
    fn from(x: system::Log<Runtime>) -> Self { InternalLog::system(x) }
}
impl From<consensus::Log<Runtime>> for Log {
    /// Converts single module log item into `$name`.
    fn from(x: consensus::Log<Runtime>) -> Self { Log(x.into()) }
}
impl From<consensus::Log<Runtime>> for InternalLog {
    /// Converts single module log item into `$internal`.
    fn from(x: consensus::Log<Runtime>) -> Self { InternalLog::consensus(x) }
}
impl From<grandpa::Log<Runtime>> for Log {
    /// Converts single module log item into `$name`.
    fn from(x: grandpa::Log<Runtime>) -> Self { Log(x.into()) }
}
impl From<grandpa::Log<Runtime>> for InternalLog {
    /// Converts single module log item into `$internal`.
    fn from(x: grandpa::Log<Runtime>) -> Self { InternalLog::grandpa(x) }
}
#[cfg(any(feature = "std", test))]
pub type SystemConfig = system::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type TimestampConfig = timestamp::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type ConsensusConfig = consensus::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type IndicesConfig = indices::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type BalancesConfig = balances::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type SessionConfig = session::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type StakingConfig = staking::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type DemocracyConfig = democracy::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type CouncilVotingConfig = council_voting::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type CouncilSeatsConfig = council_seats::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type GrandpaConfig = grandpa::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type TreasuryConfig = treasury::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type ContractConfig = contract::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type SudoConfig = sudo::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct GenesisConfig {
    pub system: Option<SystemConfig>,
    pub timestamp: Option<TimestampConfig>,
    pub consensus: Option<ConsensusConfig>,
    pub indices: Option<IndicesConfig>,
    pub balances: Option<BalancesConfig>,
    pub session: Option<SessionConfig>,
    pub staking: Option<StakingConfig>,
    pub democracy: Option<DemocracyConfig>,
    pub council_voting: Option<CouncilVotingConfig>,
    pub council_seats: Option<CouncilSeatsConfig>,
    pub grandpa: Option<GrandpaConfig>,
    pub treasury: Option<TreasuryConfig>,
    pub contract: Option<ContractConfig>,
    pub sudo: Option<SudoConfig>,
}
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_SERIALIZE_FOR_GenesisConfig: () =
    {
        #[allow(unknown_lints)]
        #[allow(rust_2018_idioms)]
        extern crate serde as _serde;
        #[allow(unused_macros)]
        macro_rules! try(( $ __expr : expr ) => {
                         match $ __expr {
                         _serde :: export :: Ok ( __val ) => __val , _serde ::
                         export :: Err ( __err ) => {
                         return _serde :: export :: Err ( __err ) ; } } });
        #[automatically_derived]
        impl _serde::Serialize for GenesisConfig {
            fn serialize<__S>(&self, __serializer: __S)
             -> _serde::export::Result<__S::Ok, __S::Error> where
             __S: _serde::Serializer {
                let mut __serde_state =
                    match _serde::Serializer::serialize_struct(__serializer,
                                                               "GenesisConfig",
                                                               false as usize
                                                                   + 1 + 1 + 1
                                                                   + 1 + 1 + 1
                                                                   + 1 + 1 + 1
                                                                   + 1 + 1 + 1
                                                                   + 1 + 1) {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    };
                match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                    "system",
                                                                    &self.system)
                    {
                    _serde::export::Ok(__val) => __val,
                    _serde::export::Err(__err) => {
                        return _serde::export::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                    "timestamp",
                                                                    &self.timestamp)
                    {
                    _serde::export::Ok(__val) => __val,
                    _serde::export::Err(__err) => {
                        return _serde::export::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                    "consensus",
                                                                    &self.consensus)
                    {
                    _serde::export::Ok(__val) => __val,
                    _serde::export::Err(__err) => {
                        return _serde::export::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                    "indices",
                                                                    &self.indices)
                    {
                    _serde::export::Ok(__val) => __val,
                    _serde::export::Err(__err) => {
                        return _serde::export::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                    "balances",
                                                                    &self.balances)
                    {
                    _serde::export::Ok(__val) => __val,
                    _serde::export::Err(__err) => {
                        return _serde::export::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                    "session",
                                                                    &self.session)
                    {
                    _serde::export::Ok(__val) => __val,
                    _serde::export::Err(__err) => {
                        return _serde::export::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                    "staking",
                                                                    &self.staking)
                    {
                    _serde::export::Ok(__val) => __val,
                    _serde::export::Err(__err) => {
                        return _serde::export::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                    "democracy",
                                                                    &self.democracy)
                    {
                    _serde::export::Ok(__val) => __val,
                    _serde::export::Err(__err) => {
                        return _serde::export::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                    "councilVoting",
                                                                    &self.council_voting)
                    {
                    _serde::export::Ok(__val) => __val,
                    _serde::export::Err(__err) => {
                        return _serde::export::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                    "councilSeats",
                                                                    &self.council_seats)
                    {
                    _serde::export::Ok(__val) => __val,
                    _serde::export::Err(__err) => {
                        return _serde::export::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                    "grandpa",
                                                                    &self.grandpa)
                    {
                    _serde::export::Ok(__val) => __val,
                    _serde::export::Err(__err) => {
                        return _serde::export::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                    "treasury",
                                                                    &self.treasury)
                    {
                    _serde::export::Ok(__val) => __val,
                    _serde::export::Err(__err) => {
                        return _serde::export::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                    "contract",
                                                                    &self.contract)
                    {
                    _serde::export::Ok(__val) => __val,
                    _serde::export::Err(__err) => {
                        return _serde::export::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                    "sudo",
                                                                    &self.sudo)
                    {
                    _serde::export::Ok(__val) => __val,
                    _serde::export::Err(__err) => {
                        return _serde::export::Err(__err);
                    }
                };
                _serde::ser::SerializeStruct::end(__serde_state)
            }
        }
    };
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_DESERIALIZE_FOR_GenesisConfig: () =
    {
        #[allow(unknown_lints)]
        #[allow(rust_2018_idioms)]
        extern crate serde as _serde;
        #[allow(unused_macros)]
        macro_rules! try(( $ __expr : expr ) => {
                         match $ __expr {
                         _serde :: export :: Ok ( __val ) => __val , _serde ::
                         export :: Err ( __err ) => {
                         return _serde :: export :: Err ( __err ) ; } } });
        #[automatically_derived]
        impl <'de> _serde::Deserialize<'de> for GenesisConfig {
            fn deserialize<__D>(__deserializer: __D)
             -> _serde::export::Result<Self, __D::Error> where
             __D: _serde::Deserializer<'de> {
                #[allow(non_camel_case_types)]
                enum __Field {
                    __field0,
                    __field1,
                    __field2,
                    __field3,
                    __field4,
                    __field5,
                    __field6,
                    __field7,
                    __field8,
                    __field9,
                    __field10,
                    __field11,
                    __field12,
                    __field13,
                }
                struct __FieldVisitor;
                impl <'de> _serde::de::Visitor<'de> for __FieldVisitor {
                    type
                    Value
                    =
                    __Field;
                    fn expecting(&self,
                                 __formatter: &mut _serde::export::Formatter)
                     -> _serde::export::fmt::Result {
                        _serde::export::Formatter::write_str(__formatter,
                                                             "field identifier")
                    }
                    fn visit_u64<__E>(self, __value: u64)
                     -> _serde::export::Result<Self::Value, __E> where
                     __E: _serde::de::Error {
                        match __value {
                            0u64 => _serde::export::Ok(__Field::__field0),
                            1u64 => _serde::export::Ok(__Field::__field1),
                            2u64 => _serde::export::Ok(__Field::__field2),
                            3u64 => _serde::export::Ok(__Field::__field3),
                            4u64 => _serde::export::Ok(__Field::__field4),
                            5u64 => _serde::export::Ok(__Field::__field5),
                            6u64 => _serde::export::Ok(__Field::__field6),
                            7u64 => _serde::export::Ok(__Field::__field7),
                            8u64 => _serde::export::Ok(__Field::__field8),
                            9u64 => _serde::export::Ok(__Field::__field9),
                            10u64 => _serde::export::Ok(__Field::__field10),
                            11u64 => _serde::export::Ok(__Field::__field11),
                            12u64 => _serde::export::Ok(__Field::__field12),
                            13u64 => _serde::export::Ok(__Field::__field13),
                            _ =>
                            _serde::export::Err(_serde::de::Error::invalid_value(_serde::de::Unexpected::Unsigned(__value),
                                                                                 &"field index 0 <= i < 14")),
                        }
                    }
                    fn visit_str<__E>(self, __value: &str)
                     -> _serde::export::Result<Self::Value, __E> where
                     __E: _serde::de::Error {
                        match __value {
                            "system" => _serde::export::Ok(__Field::__field0),
                            "timestamp" =>
                            _serde::export::Ok(__Field::__field1),
                            "consensus" =>
                            _serde::export::Ok(__Field::__field2),
                            "indices" =>
                            _serde::export::Ok(__Field::__field3),
                            "balances" =>
                            _serde::export::Ok(__Field::__field4),
                            "session" =>
                            _serde::export::Ok(__Field::__field5),
                            "staking" =>
                            _serde::export::Ok(__Field::__field6),
                            "democracy" =>
                            _serde::export::Ok(__Field::__field7),
                            "councilVoting" =>
                            _serde::export::Ok(__Field::__field8),
                            "councilSeats" =>
                            _serde::export::Ok(__Field::__field9),
                            "grandpa" =>
                            _serde::export::Ok(__Field::__field10),
                            "treasury" =>
                            _serde::export::Ok(__Field::__field11),
                            "contract" =>
                            _serde::export::Ok(__Field::__field12),
                            "sudo" => _serde::export::Ok(__Field::__field13),
                            _ => {
                                _serde::export::Err(_serde::de::Error::unknown_field(__value,
                                                                                     FIELDS))
                            }
                        }
                    }
                    fn visit_bytes<__E>(self, __value: &[u8])
                     -> _serde::export::Result<Self::Value, __E> where
                     __E: _serde::de::Error {
                        match __value {
                            b"system" =>
                            _serde::export::Ok(__Field::__field0),
                            b"timestamp" =>
                            _serde::export::Ok(__Field::__field1),
                            b"consensus" =>
                            _serde::export::Ok(__Field::__field2),
                            b"indices" =>
                            _serde::export::Ok(__Field::__field3),
                            b"balances" =>
                            _serde::export::Ok(__Field::__field4),
                            b"session" =>
                            _serde::export::Ok(__Field::__field5),
                            b"staking" =>
                            _serde::export::Ok(__Field::__field6),
                            b"democracy" =>
                            _serde::export::Ok(__Field::__field7),
                            b"councilVoting" =>
                            _serde::export::Ok(__Field::__field8),
                            b"councilSeats" =>
                            _serde::export::Ok(__Field::__field9),
                            b"grandpa" =>
                            _serde::export::Ok(__Field::__field10),
                            b"treasury" =>
                            _serde::export::Ok(__Field::__field11),
                            b"contract" =>
                            _serde::export::Ok(__Field::__field12),
                            b"sudo" => _serde::export::Ok(__Field::__field13),
                            _ => {
                                let __value =
                                    &_serde::export::from_utf8_lossy(__value);
                                _serde::export::Err(_serde::de::Error::unknown_field(__value,
                                                                                     FIELDS))
                            }
                        }
                    }
                }
                impl <'de> _serde::Deserialize<'de> for __Field {
                    #[inline]
                    fn deserialize<__D>(__deserializer: __D)
                     -> _serde::export::Result<Self, __D::Error> where
                     __D: _serde::Deserializer<'de> {
                        _serde::Deserializer::deserialize_identifier(__deserializer,
                                                                     __FieldVisitor)
                    }
                }
                struct __Visitor<'de> {
                    marker: _serde::export::PhantomData<GenesisConfig>,
                    lifetime: _serde::export::PhantomData<&'de ()>,
                }
                impl <'de> _serde::de::Visitor<'de> for __Visitor<'de> {
                    type
                    Value
                    =
                    GenesisConfig;
                    fn expecting(&self,
                                 __formatter: &mut _serde::export::Formatter)
                     -> _serde::export::fmt::Result {
                        _serde::export::Formatter::write_str(__formatter,
                                                             "struct GenesisConfig")
                    }
                    #[inline]
                    fn visit_seq<__A>(self, mut __seq: __A)
                     -> _serde::export::Result<Self::Value, __A::Error> where
                     __A: _serde::de::SeqAccess<'de> {
                        let __field0 =
                            match match _serde::de::SeqAccess::next_element::<Option<SystemConfig>>(&mut __seq)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                                _serde::export::Some(__value) => __value,
                                _serde::export::None => {
                                    return _serde::export::Err(_serde::de::Error::invalid_length(0usize,
                                                                                                 &"struct GenesisConfig with 14 elements"));
                                }
                            };
                        let __field1 =
                            match match _serde::de::SeqAccess::next_element::<Option<TimestampConfig>>(&mut __seq)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                                _serde::export::Some(__value) => __value,
                                _serde::export::None => {
                                    return _serde::export::Err(_serde::de::Error::invalid_length(1usize,
                                                                                                 &"struct GenesisConfig with 14 elements"));
                                }
                            };
                        let __field2 =
                            match match _serde::de::SeqAccess::next_element::<Option<ConsensusConfig>>(&mut __seq)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                                _serde::export::Some(__value) => __value,
                                _serde::export::None => {
                                    return _serde::export::Err(_serde::de::Error::invalid_length(2usize,
                                                                                                 &"struct GenesisConfig with 14 elements"));
                                }
                            };
                        let __field3 =
                            match match _serde::de::SeqAccess::next_element::<Option<IndicesConfig>>(&mut __seq)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                                _serde::export::Some(__value) => __value,
                                _serde::export::None => {
                                    return _serde::export::Err(_serde::de::Error::invalid_length(3usize,
                                                                                                 &"struct GenesisConfig with 14 elements"));
                                }
                            };
                        let __field4 =
                            match match _serde::de::SeqAccess::next_element::<Option<BalancesConfig>>(&mut __seq)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                                _serde::export::Some(__value) => __value,
                                _serde::export::None => {
                                    return _serde::export::Err(_serde::de::Error::invalid_length(4usize,
                                                                                                 &"struct GenesisConfig with 14 elements"));
                                }
                            };
                        let __field5 =
                            match match _serde::de::SeqAccess::next_element::<Option<SessionConfig>>(&mut __seq)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                                _serde::export::Some(__value) => __value,
                                _serde::export::None => {
                                    return _serde::export::Err(_serde::de::Error::invalid_length(5usize,
                                                                                                 &"struct GenesisConfig with 14 elements"));
                                }
                            };
                        let __field6 =
                            match match _serde::de::SeqAccess::next_element::<Option<StakingConfig>>(&mut __seq)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                                _serde::export::Some(__value) => __value,
                                _serde::export::None => {
                                    return _serde::export::Err(_serde::de::Error::invalid_length(6usize,
                                                                                                 &"struct GenesisConfig with 14 elements"));
                                }
                            };
                        let __field7 =
                            match match _serde::de::SeqAccess::next_element::<Option<DemocracyConfig>>(&mut __seq)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                                _serde::export::Some(__value) => __value,
                                _serde::export::None => {
                                    return _serde::export::Err(_serde::de::Error::invalid_length(7usize,
                                                                                                 &"struct GenesisConfig with 14 elements"));
                                }
                            };
                        let __field8 =
                            match match _serde::de::SeqAccess::next_element::<Option<CouncilVotingConfig>>(&mut __seq)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                                _serde::export::Some(__value) => __value,
                                _serde::export::None => {
                                    return _serde::export::Err(_serde::de::Error::invalid_length(8usize,
                                                                                                 &"struct GenesisConfig with 14 elements"));
                                }
                            };
                        let __field9 =
                            match match _serde::de::SeqAccess::next_element::<Option<CouncilSeatsConfig>>(&mut __seq)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                                _serde::export::Some(__value) => __value,
                                _serde::export::None => {
                                    return _serde::export::Err(_serde::de::Error::invalid_length(9usize,
                                                                                                 &"struct GenesisConfig with 14 elements"));
                                }
                            };
                        let __field10 =
                            match match _serde::de::SeqAccess::next_element::<Option<GrandpaConfig>>(&mut __seq)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                                _serde::export::Some(__value) => __value,
                                _serde::export::None => {
                                    return _serde::export::Err(_serde::de::Error::invalid_length(10usize,
                                                                                                 &"struct GenesisConfig with 14 elements"));
                                }
                            };
                        let __field11 =
                            match match _serde::de::SeqAccess::next_element::<Option<TreasuryConfig>>(&mut __seq)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                                _serde::export::Some(__value) => __value,
                                _serde::export::None => {
                                    return _serde::export::Err(_serde::de::Error::invalid_length(11usize,
                                                                                                 &"struct GenesisConfig with 14 elements"));
                                }
                            };
                        let __field12 =
                            match match _serde::de::SeqAccess::next_element::<Option<ContractConfig>>(&mut __seq)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                                _serde::export::Some(__value) => __value,
                                _serde::export::None => {
                                    return _serde::export::Err(_serde::de::Error::invalid_length(12usize,
                                                                                                 &"struct GenesisConfig with 14 elements"));
                                }
                            };
                        let __field13 =
                            match match _serde::de::SeqAccess::next_element::<Option<SudoConfig>>(&mut __seq)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                                _serde::export::Some(__value) => __value,
                                _serde::export::None => {
                                    return _serde::export::Err(_serde::de::Error::invalid_length(13usize,
                                                                                                 &"struct GenesisConfig with 14 elements"));
                                }
                            };
                        _serde::export::Ok(GenesisConfig{system: __field0,
                                                         timestamp: __field1,
                                                         consensus: __field2,
                                                         indices: __field3,
                                                         balances: __field4,
                                                         session: __field5,
                                                         staking: __field6,
                                                         democracy: __field7,
                                                         council_voting:
                                                             __field8,
                                                         council_seats:
                                                             __field9,
                                                         grandpa: __field10,
                                                         treasury: __field11,
                                                         contract: __field12,
                                                         sudo: __field13,})
                    }
                    #[inline]
                    fn visit_map<__A>(self, mut __map: __A)
                     -> _serde::export::Result<Self::Value, __A::Error> where
                     __A: _serde::de::MapAccess<'de> {
                        let mut __field0:
                                _serde::export::Option<Option<SystemConfig>> =
                            _serde::export::None;
                        let mut __field1:
                                _serde::export::Option<Option<TimestampConfig>> =
                            _serde::export::None;
                        let mut __field2:
                                _serde::export::Option<Option<ConsensusConfig>> =
                            _serde::export::None;
                        let mut __field3:
                                _serde::export::Option<Option<IndicesConfig>> =
                            _serde::export::None;
                        let mut __field4:
                                _serde::export::Option<Option<BalancesConfig>> =
                            _serde::export::None;
                        let mut __field5:
                                _serde::export::Option<Option<SessionConfig>> =
                            _serde::export::None;
                        let mut __field6:
                                _serde::export::Option<Option<StakingConfig>> =
                            _serde::export::None;
                        let mut __field7:
                                _serde::export::Option<Option<DemocracyConfig>> =
                            _serde::export::None;
                        let mut __field8:
                                _serde::export::Option<Option<CouncilVotingConfig>> =
                            _serde::export::None;
                        let mut __field9:
                                _serde::export::Option<Option<CouncilSeatsConfig>> =
                            _serde::export::None;
                        let mut __field10:
                                _serde::export::Option<Option<GrandpaConfig>> =
                            _serde::export::None;
                        let mut __field11:
                                _serde::export::Option<Option<TreasuryConfig>> =
                            _serde::export::None;
                        let mut __field12:
                                _serde::export::Option<Option<ContractConfig>> =
                            _serde::export::None;
                        let mut __field13:
                                _serde::export::Option<Option<SudoConfig>> =
                            _serde::export::None;
                        while let _serde::export::Some(__key) =
                                  match _serde::de::MapAccess::next_key::<__Field>(&mut __map)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                            match __key {
                                __Field::__field0 => {
                                    if _serde::export::Option::is_some(&__field0)
                                       {
                                        return _serde::export::Err(<__A::Error
                                                                       as
                                                                       _serde::de::Error>::duplicate_field("system"));
                                    }
                                    __field0 =
                                        _serde::export::Some(match _serde::de::MapAccess::next_value::<Option<SystemConfig>>(&mut __map)
                                                                 {
                                                                 _serde::export::Ok(__val)
                                                                 => __val,
                                                                 _serde::export::Err(__err)
                                                                 => {
                                                                     return _serde::export::Err(__err);
                                                                 }
                                                             });
                                }
                                __Field::__field1 => {
                                    if _serde::export::Option::is_some(&__field1)
                                       {
                                        return _serde::export::Err(<__A::Error
                                                                       as
                                                                       _serde::de::Error>::duplicate_field("timestamp"));
                                    }
                                    __field1 =
                                        _serde::export::Some(match _serde::de::MapAccess::next_value::<Option<TimestampConfig>>(&mut __map)
                                                                 {
                                                                 _serde::export::Ok(__val)
                                                                 => __val,
                                                                 _serde::export::Err(__err)
                                                                 => {
                                                                     return _serde::export::Err(__err);
                                                                 }
                                                             });
                                }
                                __Field::__field2 => {
                                    if _serde::export::Option::is_some(&__field2)
                                       {
                                        return _serde::export::Err(<__A::Error
                                                                       as
                                                                       _serde::de::Error>::duplicate_field("consensus"));
                                    }
                                    __field2 =
                                        _serde::export::Some(match _serde::de::MapAccess::next_value::<Option<ConsensusConfig>>(&mut __map)
                                                                 {
                                                                 _serde::export::Ok(__val)
                                                                 => __val,
                                                                 _serde::export::Err(__err)
                                                                 => {
                                                                     return _serde::export::Err(__err);
                                                                 }
                                                             });
                                }
                                __Field::__field3 => {
                                    if _serde::export::Option::is_some(&__field3)
                                       {
                                        return _serde::export::Err(<__A::Error
                                                                       as
                                                                       _serde::de::Error>::duplicate_field("indices"));
                                    }
                                    __field3 =
                                        _serde::export::Some(match _serde::de::MapAccess::next_value::<Option<IndicesConfig>>(&mut __map)
                                                                 {
                                                                 _serde::export::Ok(__val)
                                                                 => __val,
                                                                 _serde::export::Err(__err)
                                                                 => {
                                                                     return _serde::export::Err(__err);
                                                                 }
                                                             });
                                }
                                __Field::__field4 => {
                                    if _serde::export::Option::is_some(&__field4)
                                       {
                                        return _serde::export::Err(<__A::Error
                                                                       as
                                                                       _serde::de::Error>::duplicate_field("balances"));
                                    }
                                    __field4 =
                                        _serde::export::Some(match _serde::de::MapAccess::next_value::<Option<BalancesConfig>>(&mut __map)
                                                                 {
                                                                 _serde::export::Ok(__val)
                                                                 => __val,
                                                                 _serde::export::Err(__err)
                                                                 => {
                                                                     return _serde::export::Err(__err);
                                                                 }
                                                             });
                                }
                                __Field::__field5 => {
                                    if _serde::export::Option::is_some(&__field5)
                                       {
                                        return _serde::export::Err(<__A::Error
                                                                       as
                                                                       _serde::de::Error>::duplicate_field("session"));
                                    }
                                    __field5 =
                                        _serde::export::Some(match _serde::de::MapAccess::next_value::<Option<SessionConfig>>(&mut __map)
                                                                 {
                                                                 _serde::export::Ok(__val)
                                                                 => __val,
                                                                 _serde::export::Err(__err)
                                                                 => {
                                                                     return _serde::export::Err(__err);
                                                                 }
                                                             });
                                }
                                __Field::__field6 => {
                                    if _serde::export::Option::is_some(&__field6)
                                       {
                                        return _serde::export::Err(<__A::Error
                                                                       as
                                                                       _serde::de::Error>::duplicate_field("staking"));
                                    }
                                    __field6 =
                                        _serde::export::Some(match _serde::de::MapAccess::next_value::<Option<StakingConfig>>(&mut __map)
                                                                 {
                                                                 _serde::export::Ok(__val)
                                                                 => __val,
                                                                 _serde::export::Err(__err)
                                                                 => {
                                                                     return _serde::export::Err(__err);
                                                                 }
                                                             });
                                }
                                __Field::__field7 => {
                                    if _serde::export::Option::is_some(&__field7)
                                       {
                                        return _serde::export::Err(<__A::Error
                                                                       as
                                                                       _serde::de::Error>::duplicate_field("democracy"));
                                    }
                                    __field7 =
                                        _serde::export::Some(match _serde::de::MapAccess::next_value::<Option<DemocracyConfig>>(&mut __map)
                                                                 {
                                                                 _serde::export::Ok(__val)
                                                                 => __val,
                                                                 _serde::export::Err(__err)
                                                                 => {
                                                                     return _serde::export::Err(__err);
                                                                 }
                                                             });
                                }
                                __Field::__field8 => {
                                    if _serde::export::Option::is_some(&__field8)
                                       {
                                        return _serde::export::Err(<__A::Error
                                                                       as
                                                                       _serde::de::Error>::duplicate_field("councilVoting"));
                                    }
                                    __field8 =
                                        _serde::export::Some(match _serde::de::MapAccess::next_value::<Option<CouncilVotingConfig>>(&mut __map)
                                                                 {
                                                                 _serde::export::Ok(__val)
                                                                 => __val,
                                                                 _serde::export::Err(__err)
                                                                 => {
                                                                     return _serde::export::Err(__err);
                                                                 }
                                                             });
                                }
                                __Field::__field9 => {
                                    if _serde::export::Option::is_some(&__field9)
                                       {
                                        return _serde::export::Err(<__A::Error
                                                                       as
                                                                       _serde::de::Error>::duplicate_field("councilSeats"));
                                    }
                                    __field9 =
                                        _serde::export::Some(match _serde::de::MapAccess::next_value::<Option<CouncilSeatsConfig>>(&mut __map)
                                                                 {
                                                                 _serde::export::Ok(__val)
                                                                 => __val,
                                                                 _serde::export::Err(__err)
                                                                 => {
                                                                     return _serde::export::Err(__err);
                                                                 }
                                                             });
                                }
                                __Field::__field10 => {
                                    if _serde::export::Option::is_some(&__field10)
                                       {
                                        return _serde::export::Err(<__A::Error
                                                                       as
                                                                       _serde::de::Error>::duplicate_field("grandpa"));
                                    }
                                    __field10 =
                                        _serde::export::Some(match _serde::de::MapAccess::next_value::<Option<GrandpaConfig>>(&mut __map)
                                                                 {
                                                                 _serde::export::Ok(__val)
                                                                 => __val,
                                                                 _serde::export::Err(__err)
                                                                 => {
                                                                     return _serde::export::Err(__err);
                                                                 }
                                                             });
                                }
                                __Field::__field11 => {
                                    if _serde::export::Option::is_some(&__field11)
                                       {
                                        return _serde::export::Err(<__A::Error
                                                                       as
                                                                       _serde::de::Error>::duplicate_field("treasury"));
                                    }
                                    __field11 =
                                        _serde::export::Some(match _serde::de::MapAccess::next_value::<Option<TreasuryConfig>>(&mut __map)
                                                                 {
                                                                 _serde::export::Ok(__val)
                                                                 => __val,
                                                                 _serde::export::Err(__err)
                                                                 => {
                                                                     return _serde::export::Err(__err);
                                                                 }
                                                             });
                                }
                                __Field::__field12 => {
                                    if _serde::export::Option::is_some(&__field12)
                                       {
                                        return _serde::export::Err(<__A::Error
                                                                       as
                                                                       _serde::de::Error>::duplicate_field("contract"));
                                    }
                                    __field12 =
                                        _serde::export::Some(match _serde::de::MapAccess::next_value::<Option<ContractConfig>>(&mut __map)
                                                                 {
                                                                 _serde::export::Ok(__val)
                                                                 => __val,
                                                                 _serde::export::Err(__err)
                                                                 => {
                                                                     return _serde::export::Err(__err);
                                                                 }
                                                             });
                                }
                                __Field::__field13 => {
                                    if _serde::export::Option::is_some(&__field13)
                                       {
                                        return _serde::export::Err(<__A::Error
                                                                       as
                                                                       _serde::de::Error>::duplicate_field("sudo"));
                                    }
                                    __field13 =
                                        _serde::export::Some(match _serde::de::MapAccess::next_value::<Option<SudoConfig>>(&mut __map)
                                                                 {
                                                                 _serde::export::Ok(__val)
                                                                 => __val,
                                                                 _serde::export::Err(__err)
                                                                 => {
                                                                     return _serde::export::Err(__err);
                                                                 }
                                                             });
                                }
                            }
                        }
                        let __field0 =
                            match __field0 {
                                _serde::export::Some(__field0) => __field0,
                                _serde::export::None =>
                                match _serde::private::de::missing_field("system")
                                    {
                                    _serde::export::Ok(__val) => __val,
                                    _serde::export::Err(__err) => {
                                        return _serde::export::Err(__err);
                                    }
                                },
                            };
                        let __field1 =
                            match __field1 {
                                _serde::export::Some(__field1) => __field1,
                                _serde::export::None =>
                                match _serde::private::de::missing_field("timestamp")
                                    {
                                    _serde::export::Ok(__val) => __val,
                                    _serde::export::Err(__err) => {
                                        return _serde::export::Err(__err);
                                    }
                                },
                            };
                        let __field2 =
                            match __field2 {
                                _serde::export::Some(__field2) => __field2,
                                _serde::export::None =>
                                match _serde::private::de::missing_field("consensus")
                                    {
                                    _serde::export::Ok(__val) => __val,
                                    _serde::export::Err(__err) => {
                                        return _serde::export::Err(__err);
                                    }
                                },
                            };
                        let __field3 =
                            match __field3 {
                                _serde::export::Some(__field3) => __field3,
                                _serde::export::None =>
                                match _serde::private::de::missing_field("indices")
                                    {
                                    _serde::export::Ok(__val) => __val,
                                    _serde::export::Err(__err) => {
                                        return _serde::export::Err(__err);
                                    }
                                },
                            };
                        let __field4 =
                            match __field4 {
                                _serde::export::Some(__field4) => __field4,
                                _serde::export::None =>
                                match _serde::private::de::missing_field("balances")
                                    {
                                    _serde::export::Ok(__val) => __val,
                                    _serde::export::Err(__err) => {
                                        return _serde::export::Err(__err);
                                    }
                                },
                            };
                        let __field5 =
                            match __field5 {
                                _serde::export::Some(__field5) => __field5,
                                _serde::export::None =>
                                match _serde::private::de::missing_field("session")
                                    {
                                    _serde::export::Ok(__val) => __val,
                                    _serde::export::Err(__err) => {
                                        return _serde::export::Err(__err);
                                    }
                                },
                            };
                        let __field6 =
                            match __field6 {
                                _serde::export::Some(__field6) => __field6,
                                _serde::export::None =>
                                match _serde::private::de::missing_field("staking")
                                    {
                                    _serde::export::Ok(__val) => __val,
                                    _serde::export::Err(__err) => {
                                        return _serde::export::Err(__err);
                                    }
                                },
                            };
                        let __field7 =
                            match __field7 {
                                _serde::export::Some(__field7) => __field7,
                                _serde::export::None =>
                                match _serde::private::de::missing_field("democracy")
                                    {
                                    _serde::export::Ok(__val) => __val,
                                    _serde::export::Err(__err) => {
                                        return _serde::export::Err(__err);
                                    }
                                },
                            };
                        let __field8 =
                            match __field8 {
                                _serde::export::Some(__field8) => __field8,
                                _serde::export::None =>
                                match _serde::private::de::missing_field("councilVoting")
                                    {
                                    _serde::export::Ok(__val) => __val,
                                    _serde::export::Err(__err) => {
                                        return _serde::export::Err(__err);
                                    }
                                },
                            };
                        let __field9 =
                            match __field9 {
                                _serde::export::Some(__field9) => __field9,
                                _serde::export::None =>
                                match _serde::private::de::missing_field("councilSeats")
                                    {
                                    _serde::export::Ok(__val) => __val,
                                    _serde::export::Err(__err) => {
                                        return _serde::export::Err(__err);
                                    }
                                },
                            };
                        let __field10 =
                            match __field10 {
                                _serde::export::Some(__field10) => __field10,
                                _serde::export::None =>
                                match _serde::private::de::missing_field("grandpa")
                                    {
                                    _serde::export::Ok(__val) => __val,
                                    _serde::export::Err(__err) => {
                                        return _serde::export::Err(__err);
                                    }
                                },
                            };
                        let __field11 =
                            match __field11 {
                                _serde::export::Some(__field11) => __field11,
                                _serde::export::None =>
                                match _serde::private::de::missing_field("treasury")
                                    {
                                    _serde::export::Ok(__val) => __val,
                                    _serde::export::Err(__err) => {
                                        return _serde::export::Err(__err);
                                    }
                                },
                            };
                        let __field12 =
                            match __field12 {
                                _serde::export::Some(__field12) => __field12,
                                _serde::export::None =>
                                match _serde::private::de::missing_field("contract")
                                    {
                                    _serde::export::Ok(__val) => __val,
                                    _serde::export::Err(__err) => {
                                        return _serde::export::Err(__err);
                                    }
                                },
                            };
                        let __field13 =
                            match __field13 {
                                _serde::export::Some(__field13) => __field13,
                                _serde::export::None =>
                                match _serde::private::de::missing_field("sudo")
                                    {
                                    _serde::export::Ok(__val) => __val,
                                    _serde::export::Err(__err) => {
                                        return _serde::export::Err(__err);
                                    }
                                },
                            };
                        _serde::export::Ok(GenesisConfig{system: __field0,
                                                         timestamp: __field1,
                                                         consensus: __field2,
                                                         indices: __field3,
                                                         balances: __field4,
                                                         session: __field5,
                                                         staking: __field6,
                                                         democracy: __field7,
                                                         council_voting:
                                                             __field8,
                                                         council_seats:
                                                             __field9,
                                                         grandpa: __field10,
                                                         treasury: __field11,
                                                         contract: __field12,
                                                         sudo: __field13,})
                    }
                }
                const FIELDS: &'static [&'static str] =
                    &["system", "timestamp", "consensus", "indices",
                      "balances", "session", "staking", "democracy",
                      "councilVoting", "councilSeats", "grandpa", "treasury",
                      "contract", "sudo"];
                _serde::Deserializer::deserialize_struct(__deserializer,
                                                         "GenesisConfig",
                                                         FIELDS,
                                                         __Visitor{marker:
                                                                       _serde::export::PhantomData::<GenesisConfig>,
                                                                   lifetime:
                                                                       _serde::export::PhantomData,})
            }
        }
    };
#[cfg(any(feature = "std", test))]
impl $crate::BuildStorage for GenesisConfig {
    fn build_storage(self)
     ->
         ::std::result::Result<($crate::StorageMap,
                                $crate::ChildrenStorageMap), String> {
        let mut top = $crate::StorageMap::new();
        let mut children = $crate::ChildrenStorageMap::new();
        if let Some(extra) = self.system {
            let (other_top, other_children) = extra.build_storage()?;
            top.extend(other_top);
            for (other_child_key, other_child_map) in other_children {
                children.entry(other_child_key).or_default().extend(other_child_map);
            }
        }
        if let Some(extra) = self.timestamp {
            let (other_top, other_children) = extra.build_storage()?;
            top.extend(other_top);
            for (other_child_key, other_child_map) in other_children {
                children.entry(other_child_key).or_default().extend(other_child_map);
            }
        }
        if let Some(extra) = self.consensus {
            let (other_top, other_children) = extra.build_storage()?;
            top.extend(other_top);
            for (other_child_key, other_child_map) in other_children {
                children.entry(other_child_key).or_default().extend(other_child_map);
            }
        }
        if let Some(extra) = self.indices {
            let (other_top, other_children) = extra.build_storage()?;
            top.extend(other_top);
            for (other_child_key, other_child_map) in other_children {
                children.entry(other_child_key).or_default().extend(other_child_map);
            }
        }
        if let Some(extra) = self.balances {
            let (other_top, other_children) = extra.build_storage()?;
            top.extend(other_top);
            for (other_child_key, other_child_map) in other_children {
                children.entry(other_child_key).or_default().extend(other_child_map);
            }
        }
        if let Some(extra) = self.session {
            let (other_top, other_children) = extra.build_storage()?;
            top.extend(other_top);
            for (other_child_key, other_child_map) in other_children {
                children.entry(other_child_key).or_default().extend(other_child_map);
            }
        }
        if let Some(extra) = self.staking {
            let (other_top, other_children) = extra.build_storage()?;
            top.extend(other_top);
            for (other_child_key, other_child_map) in other_children {
                children.entry(other_child_key).or_default().extend(other_child_map);
            }
        }
        if let Some(extra) = self.democracy {
            let (other_top, other_children) = extra.build_storage()?;
            top.extend(other_top);
            for (other_child_key, other_child_map) in other_children {
                children.entry(other_child_key).or_default().extend(other_child_map);
            }
        }
        if let Some(extra) = self.council_voting {
            let (other_top, other_children) = extra.build_storage()?;
            top.extend(other_top);
            for (other_child_key, other_child_map) in other_children {
                children.entry(other_child_key).or_default().extend(other_child_map);
            }
        }
        if let Some(extra) = self.council_seats {
            let (other_top, other_children) = extra.build_storage()?;
            top.extend(other_top);
            for (other_child_key, other_child_map) in other_children {
                children.entry(other_child_key).or_default().extend(other_child_map);
            }
        }
        if let Some(extra) = self.grandpa {
            let (other_top, other_children) = extra.build_storage()?;
            top.extend(other_top);
            for (other_child_key, other_child_map) in other_children {
                children.entry(other_child_key).or_default().extend(other_child_map);
            }
        }
        if let Some(extra) = self.treasury {
            let (other_top, other_children) = extra.build_storage()?;
            top.extend(other_top);
            for (other_child_key, other_child_map) in other_children {
                children.entry(other_child_key).or_default().extend(other_child_map);
            }
        }
        if let Some(extra) = self.contract {
            let (other_top, other_children) = extra.build_storage()?;
            top.extend(other_top);
            for (other_child_key, other_child_map) in other_children {
                children.entry(other_child_key).or_default().extend(other_child_map);
            }
        }
        if let Some(extra) = self.sudo {
            let (other_top, other_children) = extra.build_storage()?;
            top.extend(other_top);
            for (other_child_key, other_child_map) in other_children {
                children.entry(other_child_key).or_default().extend(other_child_map);
            }
        }
        Ok((top, children))
    }
}
trait InherentDataExt {
    fn create_extrinsics(&self)
    -> $crate::inherent::Vec<<Block as $crate::inherent::BlockT>::Extrinsic>;
    fn check_extrinsics(&self, block: &Block)
    -> $crate::inherent::CheckInherentsResult;
}
impl InherentDataExt for $crate::inherent::InherentData {
    fn create_extrinsics(&self)
     ->
         $crate::inherent::Vec<<Block as
                               $crate::inherent::BlockT>::Extrinsic> {
        use $crate::inherent::ProvideInherent;
        let mut inherents = Vec::new();
        if let Some(inherent) = Aura::create_inherent(self) {
            inherents.push(UncheckedExtrinsic::new_unsigned(Call::Timestamp(inherent)));
        }
        if let Some(inherent) = Timestamp::create_inherent(self) {
            inherents.push(UncheckedExtrinsic::new_unsigned(Call::Timestamp(inherent)));
        }
        if let Some(inherent) = Consensus::create_inherent(self) {
            inherents.push(UncheckedExtrinsic::new_unsigned(Call::Consensus(inherent)));
        }
        inherents
    }
    fn check_extrinsics(&self, block: &Block)
     -> $crate::inherent::CheckInherentsResult {
        use $crate::inherent::{ProvideInherent, IsFatalError};
        let mut result = $crate::inherent::CheckInherentsResult::new();
        for xt in block.extrinsics() {
            if $crate::inherent::Extrinsic::is_signed(xt).unwrap_or(false) {
                break ;
            }
            match xt.function {
                Call::Timestamp(ref call) => {
                    if let Err(e) = Aura::check_inherent(call, self) {
                        result.put_error(Aura::INHERENT_IDENTIFIER,
                                         &e).expect("There is only one fatal error; qed");
                        if e.is_fatal_error() { return result; }
                    }
                }
                _ => { }
            }
            match xt.function {
                Call::Timestamp(ref call) => {
                    if let Err(e) = Timestamp::check_inherent(call, self) {
                        result.put_error(Timestamp::INHERENT_IDENTIFIER,
                                         &e).expect("There is only one fatal error; qed");
                        if e.is_fatal_error() { return result; }
                    }
                }
                _ => { }
            }
            match xt.function {
                Call::Consensus(ref call) => {
                    if let Err(e) = Consensus::check_inherent(call, self) {
                        result.put_error(Consensus::INHERENT_IDENTIFIER,
                                         &e).expect("There is only one fatal error; qed");
                        if e.is_fatal_error() { return result; }
                    }
                }
                _ => { }
            }
        }
        result
    }
}
/// The address format for describing accounts.
pub type Address = <Indices as StaticLookup>::Source;
/// Block header type as expected by this runtime.
pub type Header = generic::Header<BlockNumber, BlakeTwo256, Log>;
/// Block type as expected by this runtime.
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
/// A Block signed with a Justification
pub type SignedBlock = generic::SignedBlock<Block>;
/// BlockId type as expected by this runtime.
pub type BlockId = generic::BlockId<Block>;
/// Unchecked extrinsic type as expected by this runtime.
pub type UncheckedExtrinsic
    =
    generic::UncheckedMortalCompactExtrinsic<Address, Index, Call, Signature>;
/// Extrinsic type that has already been checked.
pub type CheckedExtrinsic = generic::CheckedExtrinsic<AccountId, Index, Call>;
/// Executive: handles dispatch to the various modules.
pub type Executive
    =
    executive::Executive<Runtime, Block, system::ChainContext<Runtime>,
                         Balances, AllModules>;
#[doc(hidden)]
mod sr_api_hidden_includes_IMPL_RUNTIME_APIS {
    pub extern crate client as sr_api_client;
}
pub struct RuntimeApi {
}
#[doc = r" Implements all runtime apis for the client side."]
#[cfg(any(feature = "std", test))]
pub struct RuntimeApiImpl<C: self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::CallRuntimeAt<<Runtime
                                                                                                                       as
                                                                                                                       self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock> +
                          'static> {
    call: &'static C,
    commit_on_success: ::std::cell::RefCell<bool>,
    initialised_block: ::std::cell::RefCell<Option<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                                       as
                                                                                                                                       self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>>>,
    changes: ::std::cell::RefCell<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::OverlayedChanges>,
}
#[cfg(any(feature = "std", test))]
unsafe impl <C: self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::CallRuntimeAt<<Runtime
                                                                                                          as
                                                                                                          self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>>
 Send for RuntimeApiImpl<C> {
}
#[cfg(any(feature = "std", test))]
unsafe impl <C: self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::CallRuntimeAt<<Runtime
                                                                                                          as
                                                                                                          self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>>
 Sync for RuntimeApiImpl<C> {
}
#[cfg(any(feature = "std", test))]
impl <C: self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::CallRuntimeAt<<Runtime
                                                                                                   as
                                                                                                   self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>>
 self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ApiExt<<Runtime
                                                                                    as
                                                                                    self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>
 for RuntimeApiImpl<C> {
    fn map_api_result<F: FnOnce(&Self) -> ::std::result::Result<R, E>, R,
                      E>(&self, map_call: F) -> ::std::result::Result<R, E>
     where Self: Sized {
        *self.commit_on_success.borrow_mut() = false;
        let res = map_call(self);
        *self.commit_on_success.borrow_mut() = true;
        self.commit_on_ok(&res);
        res
    }
    fn runtime_version_at(&self,
                          at:
                              &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                   as
                                                                                                                   self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::RuntimeVersion> {
        self.call.runtime_version_at(at)
    }
}
#[cfg(any(feature = "std", test))]
impl <C: self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::CallRuntimeAt<<Runtime
                                                                                                   as
                                                                                                   self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock> +
      'static>
 self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ConstructRuntimeApi<<Runtime
                                                                                                 as
                                                                                                 self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                                                                 C>
 for RuntimeApi {
    type
    RuntimeApi
    =
    RuntimeApiImpl<C>;
    fn construct_runtime_api<'a>(call: &'a C)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ApiRef<'a,
                                                                                            Self::RuntimeApi> {
        RuntimeApiImpl{call: unsafe { ::std::mem::transmute(call) },
                       commit_on_success: true.into(),
                       initialised_block: None.into(),
                       changes: Default::default(),}.into()
    }
}
#[cfg(any(feature = "std", test))]
impl <C: self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::CallRuntimeAt<<Runtime
                                                                                                   as
                                                                                                   self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>>
 RuntimeApiImpl<C> {
    fn call_api_at<R: self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Encode +
                   self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Decode +
                   PartialEq, NC: FnOnce() ->
                   ::std::result::Result<R, &'static str> +
                   ::std::panic::UnwindSafe>(&self,
                                             at:
                                                 &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                                      as
                                                                                                                                      self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>,
                                             function: &'static str,
                                             args: Vec<u8>,
                                             native_call: Option<NC>,
                                             context:
                                                 self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ExecutionContext)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::NativeOrEncoded<R>> {
        let res =
            unsafe {
                self.call.call_api_at(at, function, args,
                                      &mut *self.changes.borrow_mut(),
                                      &mut *self.initialised_block.borrow_mut(),
                                      native_call, context)
            };
        self.commit_on_ok(&res);
        res
    }
    fn commit_on_ok<R, E>(&self, res: &::std::result::Result<R, E>) {
        if *self.commit_on_success.borrow() {
            if res.is_err() {
                self.changes.borrow_mut().discard_prospective();
            } else { self.changes.borrow_mut().commit_prospective(); }
        }
    }
}
impl client_api::runtime_decl_for_Core::Core<Block> for Runtime {
    fn version() -> RuntimeVersion { VERSION }
    fn authorities() -> Vec<SessionKey> { Consensus::authorities() }
    fn execute_block(block: Block) { Executive::execute_block(block) }
    fn initialise_block(header: &<Block as BlockT>::Header) {
        Executive::initialise_block(header)
    }
}
impl client_api::runtime_decl_for_Metadata::Metadata<Block> for Runtime {
    fn metadata() -> OpaqueMetadata { Runtime::metadata().into() }
}
impl block_builder_api::runtime_decl_for_BlockBuilder::BlockBuilder<Block> for
 Runtime {
    fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic)
     -> ApplyResult {
        Executive::apply_extrinsic(extrinsic)
    }
    fn finalise_block() -> <Block as BlockT>::Header {
        Executive::finalise_block()
    }
    fn inherent_extrinsics(data: InherentData)
     -> Vec<<Block as BlockT>::Extrinsic> {
        data.create_extrinsics()
    }
    fn check_inherents(block: Block, data: InherentData)
     -> CheckInherentsResult {
        data.check_extrinsics(&block)
    }
    fn random_seed() -> <Block as BlockT>::Hash { System::random_seed() }
}
impl client_api::runtime_decl_for_TaggedTransactionQueue::TaggedTransactionQueue<Block>
 for Runtime {
    fn validate_transaction(tx: <Block as BlockT>::Extrinsic)
     -> TransactionValidity {
        Executive::validate_transaction(tx)
    }
}
impl fg_primitives::runtime_decl_for_GrandpaApi::GrandpaApi<Block> for Runtime
 {
    fn grandpa_pending_change(digest: &DigestFor<Block>)
     -> Option<ScheduledChange<NumberFor<Block>>> {
        for log in
            digest.logs.iter().filter_map(|l|
                                              match l {
                                                  Log(InternalLog::grandpa(grandpa_signal))
                                                  => Some(grandpa_signal),
                                                  _ => None,
                                              }) {
            if let Some(change) = Grandpa::scrape_digest_change(log) {
                return Some(change);
            }
        }
        None
    }
    fn grandpa_authorities() -> Vec<(SessionKey, u64)> {
        Grandpa::grandpa_authorities()
    }
}
impl consensus_aura::runtime_decl_for_AuraApi::AuraApi<Block> for Runtime {
    fn slot_duration() -> u64 { Aura::slot_duration() }
}
#[cfg(any(feature = "std", test))]
impl <RuntimeApiImplCall: self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::CallRuntimeAt<<Runtime
                                                                                                                    as
                                                                                                                    self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock> +
      'static>
 client_api::Core<<Runtime as
                  self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>
 for RuntimeApiImpl<RuntimeApiImplCall> {
    fn version_runtime_api_impl(&self,
                                at:
                                    &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                         as
                                                                                                                         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>,
                                context:
                                    self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ExecutionContext,
                                params: Option<()>, params_encoded: Vec<u8>)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::NativeOrEncoded<RuntimeVersion>> {
        self.call_api_at(at, "Core_version", params_encoded,
                         params.map(|p|
                                        {
                                            client_api::runtime_decl_for_Core::version_native_call_generator::<Runtime,
                                                                                                               <Runtime
                                                                                                               as
                                                                                                               self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                                                                               Block>()
                                        }), context)
    }
    fn authorities_runtime_api_impl(&self,
                                    at:
                                        &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                             as
                                                                                                                             self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>,
                                    context:
                                        self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ExecutionContext,
                                    params: Option<()>,
                                    params_encoded: Vec<u8>)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::NativeOrEncoded<Vec<SessionKey>>> {
        self.call_api_at(at, "Core_authorities", params_encoded,
                         params.map(|p|
                                        {
                                            client_api::runtime_decl_for_Core::authorities_native_call_generator::<Runtime,
                                                                                                                   <Runtime
                                                                                                                   as
                                                                                                                   self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                                                                                   Block>()
                                        }), context)
    }
    fn execute_block_runtime_api_impl(&self,
                                      at:
                                          &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                               as
                                                                                                                               self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>,
                                      context:
                                          self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ExecutionContext,
                                      params:
                                          Option<(<Runtime as
                                                  self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock)>,
                                      params_encoded: Vec<u8>)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::NativeOrEncoded<()>> {
        self.call_api_at(at, "Core_execute_block", params_encoded,
                         params.map(|p|
                                        {
                                            client_api::runtime_decl_for_Core::execute_block_native_call_generator::<Runtime,
                                                                                                                     <Runtime
                                                                                                                     as
                                                                                                                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                                                                                     Block>(p)
                                        }), context)
    }
    fn initialise_block_runtime_api_impl(&self,
                                         at:
                                             &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                                  as
                                                                                                                                  self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>,
                                         context:
                                             self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ExecutionContext,
                                         params:
                                             Option<(&<<Runtime as
                                                       self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock
                                                      as BlockT>::Header)>,
                                         params_encoded: Vec<u8>)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::NativeOrEncoded<()>> {
        self.call_api_at(at, "Core_initialise_block", params_encoded,
                         params.map(|p|
                                        {
                                            client_api::runtime_decl_for_Core::initialise_block_native_call_generator::<Runtime,
                                                                                                                        <Runtime
                                                                                                                        as
                                                                                                                        self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                                                                                        Block>(p)
                                        }), context)
    }
}
#[cfg(any(feature = "std", test))]
impl <RuntimeApiImplCall: self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::CallRuntimeAt<<Runtime
                                                                                                                    as
                                                                                                                    self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock> +
      'static>
 client_api::Metadata<<Runtime as
                      self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>
 for RuntimeApiImpl<RuntimeApiImplCall> {
    fn metadata_runtime_api_impl(&self,
                                 at:
                                     &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                          as
                                                                                                                          self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>,
                                 context:
                                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ExecutionContext,
                                 params: Option<()>, params_encoded: Vec<u8>)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::NativeOrEncoded<OpaqueMetadata>> {
        self.call_api_at(at, "Metadata_metadata", params_encoded,
                         params.map(|p|
                                        {
                                            client_api::runtime_decl_for_Metadata::metadata_native_call_generator::<Runtime,
                                                                                                                    <Runtime
                                                                                                                    as
                                                                                                                    self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                                                                                    Block>()
                                        }), context)
    }
}
#[cfg(any(feature = "std", test))]
impl <RuntimeApiImplCall: self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::CallRuntimeAt<<Runtime
                                                                                                                    as
                                                                                                                    self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock> +
      'static>
 block_builder_api::BlockBuilder<<Runtime as
                                 self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>
 for RuntimeApiImpl<RuntimeApiImplCall> {
    fn apply_extrinsic_runtime_api_impl(&self,
                                        at:
                                            &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                                 as
                                                                                                                                 self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>,
                                        context:
                                            self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ExecutionContext,
                                        params:
                                            Option<(<<Runtime as
                                                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock
                                                    as BlockT>::Extrinsic)>,
                                        params_encoded: Vec<u8>)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::NativeOrEncoded<ApplyResult>> {
        self.call_api_at(at, "BlockBuilder_apply_extrinsic", params_encoded,
                         params.map(|p|
                                        {
                                            block_builder_api::runtime_decl_for_BlockBuilder::apply_extrinsic_native_call_generator::<Runtime,
                                                                                                                                      <Runtime
                                                                                                                                      as
                                                                                                                                      self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                                                                                                      Block>(p)
                                        }), context)
    }
    fn finalise_block_runtime_api_impl(&self,
                                       at:
                                           &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                                as
                                                                                                                                self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>,
                                       context:
                                           self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ExecutionContext,
                                       params: Option<()>,
                                       params_encoded: Vec<u8>)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::NativeOrEncoded<<<Runtime
                                                                                                                                                                                   as
                                                                                                                                                                                   self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock
                                                                                                                                                                                  as
                                                                                                                                                                                  BlockT>::Header>> {
        self.call_api_at(at, "BlockBuilder_finalise_block", params_encoded,
                         params.map(|p|
                                        {
                                            block_builder_api::runtime_decl_for_BlockBuilder::finalise_block_native_call_generator::<Runtime,
                                                                                                                                     <Runtime
                                                                                                                                     as
                                                                                                                                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                                                                                                     Block>()
                                        }), context)
    }
    fn inherent_extrinsics_runtime_api_impl(&self,
                                            at:
                                                &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                                     as
                                                                                                                                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>,
                                            context:
                                                self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ExecutionContext,
                                            params: Option<(InherentData)>,
                                            params_encoded: Vec<u8>)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::NativeOrEncoded<Vec<<<Runtime
                                                                                                                                                                                       as
                                                                                                                                                                                       self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock
                                                                                                                                                                                      as
                                                                                                                                                                                      BlockT>::Extrinsic>>> {
        self.call_api_at(at, "BlockBuilder_inherent_extrinsics",
                         params_encoded,
                         params.map(|p|
                                        {
                                            block_builder_api::runtime_decl_for_BlockBuilder::inherent_extrinsics_native_call_generator::<Runtime,
                                                                                                                                          <Runtime
                                                                                                                                          as
                                                                                                                                          self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                                                                                                          Block>(p)
                                        }), context)
    }
    fn check_inherents_runtime_api_impl(&self,
                                        at:
                                            &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                                 as
                                                                                                                                 self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>,
                                        context:
                                            self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ExecutionContext,
                                        params:
                                            Option<(<Runtime as
                                                    self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                    InherentData)>,
                                        params_encoded: Vec<u8>)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::NativeOrEncoded<CheckInherentsResult>> {
        self.call_api_at(at, "BlockBuilder_check_inherents", params_encoded,
                         params.map(|p|
                                        {
                                            block_builder_api::runtime_decl_for_BlockBuilder::check_inherents_native_call_generator::<Runtime,
                                                                                                                                      <Runtime
                                                                                                                                      as
                                                                                                                                      self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                                                                                                      Block>(p.0,
                                                                                                                                             p.1)
                                        }), context)
    }
    fn random_seed_runtime_api_impl(&self,
                                    at:
                                        &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                             as
                                                                                                                             self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>,
                                    context:
                                        self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ExecutionContext,
                                    params: Option<()>,
                                    params_encoded: Vec<u8>)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::NativeOrEncoded<<<Runtime
                                                                                                                                                                                   as
                                                                                                                                                                                   self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock
                                                                                                                                                                                  as
                                                                                                                                                                                  BlockT>::Hash>> {
        self.call_api_at(at, "BlockBuilder_random_seed", params_encoded,
                         params.map(|p|
                                        {
                                            block_builder_api::runtime_decl_for_BlockBuilder::random_seed_native_call_generator::<Runtime,
                                                                                                                                  <Runtime
                                                                                                                                  as
                                                                                                                                  self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                                                                                                  Block>()
                                        }), context)
    }
}
#[cfg(any(feature = "std", test))]
impl <RuntimeApiImplCall: self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::CallRuntimeAt<<Runtime
                                                                                                                    as
                                                                                                                    self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock> +
      'static>
 client_api::TaggedTransactionQueue<<Runtime as
                                    self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>
 for RuntimeApiImpl<RuntimeApiImplCall> {
    fn validate_transaction_runtime_api_impl(&self,
                                             at:
                                                 &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                                      as
                                                                                                                                      self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>,
                                             context:
                                                 self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ExecutionContext,
                                             params:
                                                 Option<(<<Runtime as
                                                          self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock
                                                         as
                                                         BlockT>::Extrinsic)>,
                                             params_encoded: Vec<u8>)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::NativeOrEncoded<TransactionValidity>> {
        self.call_api_at(at, "TaggedTransactionQueue_validate_transaction",
                         params_encoded,
                         params.map(|p|
                                        {
                                            client_api::runtime_decl_for_TaggedTransactionQueue::validate_transaction_native_call_generator::<Runtime,
                                                                                                                                              <Runtime
                                                                                                                                              as
                                                                                                                                              self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                                                                                                              Block>(p)
                                        }), context)
    }
}
#[cfg(any(feature = "std", test))]
impl <RuntimeApiImplCall: self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::CallRuntimeAt<<Runtime
                                                                                                                    as
                                                                                                                    self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock> +
      'static>
 fg_primitives::GrandpaApi<<Runtime as
                           self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>
 for RuntimeApiImpl<RuntimeApiImplCall> {
    fn grandpa_pending_change_runtime_api_impl(&self,
                                               at:
                                                   &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                                        as
                                                                                                                                        self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>,
                                               context:
                                                   self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ExecutionContext,
                                               params:
                                                   Option<(&DigestFor<<Runtime
                                                                      as
                                                                      self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>)>,
                                               params_encoded: Vec<u8>)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::NativeOrEncoded<Option<ScheduledChange<NumberFor<<Runtime
                                                                                                                                                                                                                   as
                                                                                                                                                                                                                   self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>>>>> {
        self.call_api_at(at, "GrandpaApi_grandpa_pending_change",
                         params_encoded,
                         params.map(|p|
                                        {
                                            fg_primitives::runtime_decl_for_GrandpaApi::grandpa_pending_change_native_call_generator::<Runtime,
                                                                                                                                       <Runtime
                                                                                                                                       as
                                                                                                                                       self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                                                                                                       Block>(p)
                                        }), context)
    }
    fn grandpa_authorities_runtime_api_impl(&self,
                                            at:
                                                &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                                     as
                                                                                                                                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>,
                                            context:
                                                self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ExecutionContext,
                                            params: Option<()>,
                                            params_encoded: Vec<u8>)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::NativeOrEncoded<Vec<(SessionKey,
                                                                                                                                                                                       u64)>>> {
        self.call_api_at(at, "GrandpaApi_grandpa_authorities", params_encoded,
                         params.map(|p|
                                        {
                                            fg_primitives::runtime_decl_for_GrandpaApi::grandpa_authorities_native_call_generator::<Runtime,
                                                                                                                                    <Runtime
                                                                                                                                    as
                                                                                                                                    self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                                                                                                    Block>()
                                        }), context)
    }
}
#[cfg(any(feature = "std", test))]
impl <RuntimeApiImplCall: self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::CallRuntimeAt<<Runtime
                                                                                                                    as
                                                                                                                    self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock> +
      'static>
 consensus_aura::AuraApi<<Runtime as
                         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>
 for RuntimeApiImpl<RuntimeApiImplCall> {
    fn slot_duration_runtime_api_impl(&self,
                                      at:
                                          &self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::BlockId<<Runtime
                                                                                                                               as
                                                                                                                               self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock>,
                                      context:
                                          self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ExecutionContext,
                                      params: Option<()>,
                                      params_encoded: Vec<u8>)
     ->
         self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::error::Result<self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::NativeOrEncoded<u64>> {
        self.call_api_at(at, "AuraApi_slot_duration", params_encoded,
                         params.map(|p|
                                        {
                                            consensus_aura::runtime_decl_for_AuraApi::slot_duration_native_call_generator::<Runtime,
                                                                                                                            <Runtime
                                                                                                                            as
                                                                                                                            self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::GetNodeBlockType>::NodeBlock,
                                                                                                                            Block>()
                                        }), context)
    }
}
const RUNTIME_API_VERSIONS:
      self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::ApisVec
      =
    ::std::borrow::Cow::Borrowed(&[(client_api::runtime_decl_for_Core::ID,
                                    client_api::runtime_decl_for_Core::VERSION),
                                   (client_api::runtime_decl_for_Metadata::ID,
                                    client_api::runtime_decl_for_Metadata::VERSION),
                                   (block_builder_api::runtime_decl_for_BlockBuilder::ID,
                                    block_builder_api::runtime_decl_for_BlockBuilder::VERSION),
                                   (client_api::runtime_decl_for_TaggedTransactionQueue::ID,
                                    client_api::runtime_decl_for_TaggedTransactionQueue::VERSION),
                                   (fg_primitives::runtime_decl_for_GrandpaApi::ID,
                                    fg_primitives::runtime_decl_for_GrandpaApi::VERSION),
                                   (consensus_aura::runtime_decl_for_AuraApi::ID,
                                    consensus_aura::runtime_decl_for_AuraApi::VERSION)]);
pub mod api {
    use super::*;
    #[cfg(feature = "std")]
    pub fn dispatch(method: &str, mut data: &[u8]) -> Option<Vec<u8>> {
        match method {
            "Core_version" =>
            Some({
                     let output =
                         <Runtime as
                             client_api::runtime_decl_for_Core::Core<Block>>::version();
                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Encode::encode(&output)
                 }),
            "Core_authorities" =>
            Some({
                     let output =
                         <Runtime as
                             client_api::runtime_decl_for_Core::Core<Block>>::authorities();
                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Encode::encode(&output)
                 }),
            "Core_execute_block" =>
            Some({
                     let block: Block =
                         match self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Decode::decode(&mut data)
                             {
                             Some(input) => input,
                             None => {
                                 $crate::rt::begin_panic_fmt(&$crate::fmt::Arguments::new_v1_formatted(&["Bad input data provided to "],
                                                                                                       &match (&"execute_block",)
                                                                                                            {
                                                                                                            (arg0,)
                                                                                                            =>
                                                                                                            [$crate::fmt::ArgumentV1::new(arg0,
                                                                                                                                          $crate::fmt::Display::fmt)],
                                                                                                        },
                                                                                                       &[$crate::fmt::rt::v1::Argument{position:
                                                                                                                                           $crate::fmt::rt::v1::Position::At(0usize),
                                                                                                                                       format:
                                                                                                                                           $crate::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                                               ' ',
                                                                                                                                                                           align:
                                                                                                                                                                               $crate::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                                           flags:
                                                                                                                                                                               0u32,
                                                                                                                                                                           precision:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,
                                                                                                                                                                           width:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,},}]),
                                                             &("node/runtime/src/lib.rs",
                                                               238u32, 1u32))
                             }
                         };
                     let output =
                         <Runtime as
                             client_api::runtime_decl_for_Core::Core<Block>>::execute_block(block);
                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Encode::encode(&output)
                 }),
            "Core_initialise_block" =>
            Some({
                     let header: <Block as BlockT>::Header =
                         match self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Decode::decode(&mut data)
                             {
                             Some(input) => input,
                             None => {
                                 $crate::rt::begin_panic_fmt(&$crate::fmt::Arguments::new_v1_formatted(&["Bad input data provided to "],
                                                                                                       &match (&"initialise_block",)
                                                                                                            {
                                                                                                            (arg0,)
                                                                                                            =>
                                                                                                            [$crate::fmt::ArgumentV1::new(arg0,
                                                                                                                                          $crate::fmt::Display::fmt)],
                                                                                                        },
                                                                                                       &[$crate::fmt::rt::v1::Argument{position:
                                                                                                                                           $crate::fmt::rt::v1::Position::At(0usize),
                                                                                                                                       format:
                                                                                                                                           $crate::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                                               ' ',
                                                                                                                                                                           align:
                                                                                                                                                                               $crate::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                                           flags:
                                                                                                                                                                               0u32,
                                                                                                                                                                           precision:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,
                                                                                                                                                                           width:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,},}]),
                                                             &("node/runtime/src/lib.rs",
                                                               238u32, 1u32))
                             }
                         };
                     let output =
                         <Runtime as
                             client_api::runtime_decl_for_Core::Core<Block>>::initialise_block(&header);
                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Encode::encode(&output)
                 }),
            "Metadata_metadata" =>
            Some({
                     let output =
                         <Runtime as
                             client_api::runtime_decl_for_Metadata::Metadata<Block>>::metadata();
                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Encode::encode(&output)
                 }),
            "BlockBuilder_apply_extrinsic" =>
            Some({
                     let extrinsic: <Block as BlockT>::Extrinsic =
                         match self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Decode::decode(&mut data)
                             {
                             Some(input) => input,
                             None => {
                                 $crate::rt::begin_panic_fmt(&$crate::fmt::Arguments::new_v1_formatted(&["Bad input data provided to "],
                                                                                                       &match (&"apply_extrinsic",)
                                                                                                            {
                                                                                                            (arg0,)
                                                                                                            =>
                                                                                                            [$crate::fmt::ArgumentV1::new(arg0,
                                                                                                                                          $crate::fmt::Display::fmt)],
                                                                                                        },
                                                                                                       &[$crate::fmt::rt::v1::Argument{position:
                                                                                                                                           $crate::fmt::rt::v1::Position::At(0usize),
                                                                                                                                       format:
                                                                                                                                           $crate::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                                               ' ',
                                                                                                                                                                           align:
                                                                                                                                                                               $crate::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                                           flags:
                                                                                                                                                                               0u32,
                                                                                                                                                                           precision:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,
                                                                                                                                                                           width:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,},}]),
                                                             &("node/runtime/src/lib.rs",
                                                               238u32, 1u32))
                             }
                         };
                     let output =
                         <Runtime as
                             block_builder_api::runtime_decl_for_BlockBuilder::BlockBuilder<Block>>::apply_extrinsic(extrinsic);
                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Encode::encode(&output)
                 }),
            "BlockBuilder_finalise_block" =>
            Some({
                     let output =
                         <Runtime as
                             block_builder_api::runtime_decl_for_BlockBuilder::BlockBuilder<Block>>::finalise_block();
                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Encode::encode(&output)
                 }),
            "BlockBuilder_inherent_extrinsics" =>
            Some({
                     let data: InherentData =
                         match self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Decode::decode(&mut data)
                             {
                             Some(input) => input,
                             None => {
                                 $crate::rt::begin_panic_fmt(&$crate::fmt::Arguments::new_v1_formatted(&["Bad input data provided to "],
                                                                                                       &match (&"inherent_extrinsics",)
                                                                                                            {
                                                                                                            (arg0,)
                                                                                                            =>
                                                                                                            [$crate::fmt::ArgumentV1::new(arg0,
                                                                                                                                          $crate::fmt::Display::fmt)],
                                                                                                        },
                                                                                                       &[$crate::fmt::rt::v1::Argument{position:
                                                                                                                                           $crate::fmt::rt::v1::Position::At(0usize),
                                                                                                                                       format:
                                                                                                                                           $crate::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                                               ' ',
                                                                                                                                                                           align:
                                                                                                                                                                               $crate::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                                           flags:
                                                                                                                                                                               0u32,
                                                                                                                                                                           precision:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,
                                                                                                                                                                           width:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,},}]),
                                                             &("node/runtime/src/lib.rs",
                                                               238u32, 1u32))
                             }
                         };
                     let output =
                         <Runtime as
                             block_builder_api::runtime_decl_for_BlockBuilder::BlockBuilder<Block>>::inherent_extrinsics(data);
                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Encode::encode(&output)
                 }),
            "BlockBuilder_check_inherents" =>
            Some({
                     let block: Block =
                         match self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Decode::decode(&mut data)
                             {
                             Some(input) => input,
                             None => {
                                 $crate::rt::begin_panic_fmt(&$crate::fmt::Arguments::new_v1_formatted(&["Bad input data provided to "],
                                                                                                       &match (&"check_inherents",)
                                                                                                            {
                                                                                                            (arg0,)
                                                                                                            =>
                                                                                                            [$crate::fmt::ArgumentV1::new(arg0,
                                                                                                                                          $crate::fmt::Display::fmt)],
                                                                                                        },
                                                                                                       &[$crate::fmt::rt::v1::Argument{position:
                                                                                                                                           $crate::fmt::rt::v1::Position::At(0usize),
                                                                                                                                       format:
                                                                                                                                           $crate::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                                               ' ',
                                                                                                                                                                           align:
                                                                                                                                                                               $crate::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                                           flags:
                                                                                                                                                                               0u32,
                                                                                                                                                                           precision:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,
                                                                                                                                                                           width:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,},}]),
                                                             &("node/runtime/src/lib.rs",
                                                               238u32, 1u32))
                             }
                         };
                     let data: InherentData =
                         match self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Decode::decode(&mut data)
                             {
                             Some(input) => input,
                             None => {
                                 $crate::rt::begin_panic_fmt(&$crate::fmt::Arguments::new_v1_formatted(&["Bad input data provided to "],
                                                                                                       &match (&"check_inherents",)
                                                                                                            {
                                                                                                            (arg0,)
                                                                                                            =>
                                                                                                            [$crate::fmt::ArgumentV1::new(arg0,
                                                                                                                                          $crate::fmt::Display::fmt)],
                                                                                                        },
                                                                                                       &[$crate::fmt::rt::v1::Argument{position:
                                                                                                                                           $crate::fmt::rt::v1::Position::At(0usize),
                                                                                                                                       format:
                                                                                                                                           $crate::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                                               ' ',
                                                                                                                                                                           align:
                                                                                                                                                                               $crate::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                                           flags:
                                                                                                                                                                               0u32,
                                                                                                                                                                           precision:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,
                                                                                                                                                                           width:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,},}]),
                                                             &("node/runtime/src/lib.rs",
                                                               238u32, 1u32))
                             }
                         };
                     let output =
                         <Runtime as
                             block_builder_api::runtime_decl_for_BlockBuilder::BlockBuilder<Block>>::check_inherents(block,
                                                                                                                     data);
                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Encode::encode(&output)
                 }),
            "BlockBuilder_random_seed" =>
            Some({
                     let output =
                         <Runtime as
                             block_builder_api::runtime_decl_for_BlockBuilder::BlockBuilder<Block>>::random_seed();
                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Encode::encode(&output)
                 }),
            "TaggedTransactionQueue_validate_transaction" =>
            Some({
                     let tx: <Block as BlockT>::Extrinsic =
                         match self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Decode::decode(&mut data)
                             {
                             Some(input) => input,
                             None => {
                                 $crate::rt::begin_panic_fmt(&$crate::fmt::Arguments::new_v1_formatted(&["Bad input data provided to "],
                                                                                                       &match (&"validate_transaction",)
                                                                                                            {
                                                                                                            (arg0,)
                                                                                                            =>
                                                                                                            [$crate::fmt::ArgumentV1::new(arg0,
                                                                                                                                          $crate::fmt::Display::fmt)],
                                                                                                        },
                                                                                                       &[$crate::fmt::rt::v1::Argument{position:
                                                                                                                                           $crate::fmt::rt::v1::Position::At(0usize),
                                                                                                                                       format:
                                                                                                                                           $crate::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                                               ' ',
                                                                                                                                                                           align:
                                                                                                                                                                               $crate::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                                           flags:
                                                                                                                                                                               0u32,
                                                                                                                                                                           precision:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,
                                                                                                                                                                           width:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,},}]),
                                                             &("node/runtime/src/lib.rs",
                                                               238u32, 1u32))
                             }
                         };
                     let output =
                         <Runtime as
                             client_api::runtime_decl_for_TaggedTransactionQueue::TaggedTransactionQueue<Block>>::validate_transaction(tx);
                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Encode::encode(&output)
                 }),
            "GrandpaApi_grandpa_pending_change" =>
            Some({
                     let digest: DigestFor<Block> =
                         match self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Decode::decode(&mut data)
                             {
                             Some(input) => input,
                             None => {
                                 $crate::rt::begin_panic_fmt(&$crate::fmt::Arguments::new_v1_formatted(&["Bad input data provided to "],
                                                                                                       &match (&"grandpa_pending_change",)
                                                                                                            {
                                                                                                            (arg0,)
                                                                                                            =>
                                                                                                            [$crate::fmt::ArgumentV1::new(arg0,
                                                                                                                                          $crate::fmt::Display::fmt)],
                                                                                                        },
                                                                                                       &[$crate::fmt::rt::v1::Argument{position:
                                                                                                                                           $crate::fmt::rt::v1::Position::At(0usize),
                                                                                                                                       format:
                                                                                                                                           $crate::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                                               ' ',
                                                                                                                                                                           align:
                                                                                                                                                                               $crate::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                                           flags:
                                                                                                                                                                               0u32,
                                                                                                                                                                           precision:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,
                                                                                                                                                                           width:
                                                                                                                                                                               $crate::fmt::rt::v1::Count::Implied,},}]),
                                                             &("node/runtime/src/lib.rs",
                                                               238u32, 1u32))
                             }
                         };
                     let output =
                         <Runtime as
                             fg_primitives::runtime_decl_for_GrandpaApi::GrandpaApi<Block>>::grandpa_pending_change(&digest);
                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Encode::encode(&output)
                 }),
            "GrandpaApi_grandpa_authorities" =>
            Some({
                     let output =
                         <Runtime as
                             fg_primitives::runtime_decl_for_GrandpaApi::GrandpaApi<Block>>::grandpa_authorities();
                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Encode::encode(&output)
                 }),
            "AuraApi_slot_duration" =>
            Some({
                     let output =
                         <Runtime as
                             consensus_aura::runtime_decl_for_AuraApi::AuraApi<Block>>::slot_duration();
                     self::sr_api_hidden_includes_IMPL_RUNTIME_APIS::sr_api_client::runtime_api::Encode::encode(&output)
                 }),
            _ => None,
        }
    }
}
