#![feature(prelude_import)]
#![no_std]
// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! The Polkadot runtime. This can be compiled with ``#[no_std]`, ready for Wasm.
#[prelude_import]
use std::prelude::v1::*;
#[macro_use]
extern crate std;


#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[cfg(feature = "std")]
extern crate serde;

#[macro_use]
extern crate substrate_runtime_io as runtime_io;

#[macro_use]
extern crate substrate_runtime_support;

#[macro_use]
extern crate substrate_runtime_primitives as runtime_primitives;



#[macro_use]
extern crate substrate_primitives;

extern crate substrate_runtime_std as rstd;
extern crate substrate_codec as codec;
extern crate substrate_runtime_consensus as consensus;
extern crate substrate_runtime_council as council;
extern crate substrate_runtime_democracy as democracy;
extern crate substrate_runtime_executive as executive;
extern crate substrate_runtime_session as session;
extern crate substrate_runtime_staking as staking;
extern crate substrate_runtime_system as system;
extern crate substrate_runtime_timestamp as timestamp;

pub mod primitives {






    // TODO: Option<AccountId>






























    // 71000000
    // 0101010101010101010101010101010101010101010101010101010101010101
    // e703000000000000
    // 00
    // df0f0200
    // 0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000




    //! Primitive types for the polkadot runtime.
    use codec::{Slicable, Input};
    use rstd::prelude::*;
    use rstd::cmp::Ordering;
    use substrate_primitives;
    use runtime_primitives::{self, generic, traits::BlakeTwo256};
    use super::Call;
    #[cfg(feature = "std")]
    use substrate_primitives::bytes;
    /// Block header type as expected by this runtime.
    pub type Header = generic::Header<BlockNumber, BlakeTwo256, Log>;
    /// Block type as expected by this runtime.
    pub type Block =
        generic::Block<BlockNumber, BlakeTwo256, Log, AccountId, Index, Call,
                       Signature>;
    /// Unchecked extrinsic type as expected by this runtime.
    pub type UncheckedExtrinsic =
        generic::UncheckedExtrinsic<AccountId, Index, Call, Signature>;
    /// Extrinsic type as expected by this runtime.
    pub type Extrinsic = generic::Extrinsic<AccountId, Index, Call>;
    /// Something that identifies a block.
    pub type BlockId = generic::BlockId<Block>;
    /// A log entry in the block.
    #[structural_match]
    pub struct Log(
                   #[serde(with = "bytes")]
                   pub Vec<u8>);
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::std::cmp::PartialEq for Log {
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
    impl ::std::cmp::Eq for Log {
        #[inline]
        #[doc(hidden)]
        fn assert_receiver_is_total_eq(&self) -> () {
            { let _: ::std::cmp::AssertParamIsEq<Vec<u8>>; }
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::std::clone::Clone for Log {
        #[inline]
        fn clone(&self) -> Log {
            match *self {
                Log(ref __self_0_0) =>
                Log(::std::clone::Clone::clone(&(*__self_0_0))),
            }
        }
    }
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::std::default::Default for Log {
        #[inline]
        fn default() -> Log { Log(::std::default::Default::default()) }
    }
    #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
    const _IMPL_SERIALIZE_FOR_Log: () =
        {
            extern crate serde as _serde;
            #[allow(unused_macros)]
            macro_rules! try(( $ __expr : expr ) => {
                             match $ __expr {
                             _serde :: export :: Ok ( __val ) => __val ,
                             _serde :: export :: Err ( __err ) => {
                             return _serde :: export :: Err ( __err ) ; } }
                             });
            #[automatically_derived]
            impl _serde::Serialize for Log {
                fn serialize<__S>(&self, __serializer: __S)
                 -> _serde::export::Result<__S::Ok, __S::Error> where
                 __S: _serde::Serializer {
                    _serde::Serializer::serialize_newtype_struct(__serializer,
                                                                 "Log",
                                                                 {
                                                                     struct __SerializeWith<'__a> {
                                                                         values: (&'__a Vec<u8>,),
                                                                         phantom: _serde::export::PhantomData<Log>,
                                                                     }
                                                                     impl <'__a>
                                                                      _serde::Serialize
                                                                      for
                                                                      __SerializeWith<'__a>
                                                                      {
                                                                         fn serialize<__S>(&self,
                                                                                           __s:
                                                                                               __S)
                                                                          ->
                                                                              _serde::export::Result<__S::Ok,
                                                                                                     __S::Error>
                                                                          where
                                                                          __S: _serde::Serializer {
                                                                             bytes::serialize(self.values.0,
                                                                                              __s)
                                                                         }
                                                                     }
                                                                     &__SerializeWith{values:
                                                                                          (&self.0,),
                                                                                      phantom:
                                                                                          _serde::export::PhantomData::<Log>,}
                                                                 })
                }
            }
        };
    #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
    const _IMPL_DESERIALIZE_FOR_Log: () =
        {
            extern crate serde as _serde;
            #[allow(unused_macros)]
            macro_rules! try(( $ __expr : expr ) => {
                             match $ __expr {
                             _serde :: export :: Ok ( __val ) => __val ,
                             _serde :: export :: Err ( __err ) => {
                             return _serde :: export :: Err ( __err ) ; } }
                             });
            #[automatically_derived]
            impl <'de> _serde::Deserialize<'de> for Log {
                fn deserialize<__D>(__deserializer: __D)
                 -> _serde::export::Result<Self, __D::Error> where
                 __D: _serde::Deserializer<'de> {
                    struct __Visitor<'de> {
                        marker: _serde::export::PhantomData<Log>,
                        lifetime: _serde::export::PhantomData<&'de ()>,
                    }
                    impl <'de> _serde::de::Visitor<'de> for __Visitor<'de> {
                        type
                        Value
                        =
                        Log;
                        fn expecting(&self,
                                     __formatter:
                                         &mut _serde::export::Formatter)
                         -> _serde::export::fmt::Result {
                            _serde::export::Formatter::write_str(__formatter,
                                                                 "tuple struct Log")
                        }
                        #[inline]
                        fn visit_newtype_struct<__E>(self, __e: __E)
                         -> _serde::export::Result<Self::Value, __E::Error>
                         where __E: _serde::Deserializer<'de> {
                            let __field0: Vec<u8> =
                                match bytes::deserialize(__e) {
                                    _serde::export::Ok(__val) => __val,
                                    _serde::export::Err(__err) => {
                                        return _serde::export::Err(__err);
                                    }
                                };
                            _serde::export::Ok(Log(__field0))
                        }
                        #[inline]
                        fn visit_seq<__A>(self, mut __seq: __A)
                         -> _serde::export::Result<Self::Value, __A::Error>
                         where __A: _serde::de::SeqAccess<'de> {
                            let __field0 =
                                match {
                                          struct __DeserializeWith<'de> {
                                              value: Vec<u8>,
                                              phantom: _serde::export::PhantomData<Log>,
                                              lifetime: _serde::export::PhantomData<&'de ()>,
                                          }
                                          impl <'de> _serde::Deserialize<'de>
                                           for __DeserializeWith<'de> {
                                              fn deserialize<__D>(__deserializer:
                                                                      __D)
                                               ->
                                                   _serde::export::Result<Self,
                                                                          __D::Error>
                                               where
                                               __D: _serde::Deserializer<'de> {
                                                  _serde::export::Ok(__DeserializeWith{value:
                                                                                           match bytes::deserialize(__deserializer)
                                                                                               {
                                                                                               _serde::export::Ok(__val)
                                                                                               =>
                                                                                               __val,
                                                                                               _serde::export::Err(__err)
                                                                                               =>
                                                                                               {
                                                                                                   return _serde::export::Err(__err);
                                                                                               }
                                                                                           },
                                                                                       phantom:
                                                                                           _serde::export::PhantomData,
                                                                                       lifetime:
                                                                                           _serde::export::PhantomData,})
                                              }
                                          }
                                          _serde::export::Option::map(match _serde::de::SeqAccess::next_element::<__DeserializeWith<'de>>(&mut __seq)
                                                                          {
                                                                          _serde::export::Ok(__val)
                                                                          =>
                                                                          __val,
                                                                          _serde::export::Err(__err)
                                                                          => {
                                                                              return _serde::export::Err(__err);
                                                                          }
                                                                      },
                                                                      |__wrap|
                                                                          __wrap.value)
                                      } {
                                    _serde::export::Some(__value) => __value,
                                    _serde::export::None => {
                                        return _serde::export::Err(_serde::de::Error::invalid_length(0usize,
                                                                                                     &"tuple struct Log with 1 element"));
                                    }
                                };
                            _serde::export::Ok(Log(__field0))
                        }
                    }
                    _serde::Deserializer::deserialize_newtype_struct(__deserializer,
                                                                     "Log",
                                                                     __Visitor{marker:
                                                                                   _serde::export::PhantomData::<Log>,
                                                                               lifetime:
                                                                                   _serde::export::PhantomData,})
                }
            }
        };
    #[automatically_derived]
    #[allow(unused_qualifications)]
    impl ::std::fmt::Debug for Log {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
            match *self {
                Log(ref __self_0_0) => {
                    let mut debug_trait_builder = f.debug_tuple("Log");
                    let _ = debug_trait_builder.field(&&(*__self_0_0));
                    debug_trait_builder.finish()
                }
            }
        }
    }
    impl Slicable for Log {
        fn decode<I: Input>(input: &mut I) -> Option<Self> {
            Vec::<u8>::decode(input).map(Log)
        }
        fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
            self.0.using_encoded(f)
        }
    }
    /// An index to a block.
    /// 32-bits will allow for 136 years of blocks assuming 1 block per second.
    /// TODO: switch to u32
    pub type BlockNumber = u64;
    /// Alias to Ed25519 pubkey that identifies an account on the relay chain. This will almost
    /// certainly continue to be the same as the substrate's `AuthorityId`.
    pub type AccountId = substrate_primitives::hash::H256;
    /// The Ed25519 pub key of an session that belongs to an authority of the relay chain. This is
    /// exactly equivalent to what the substrate calls an "authority".
    pub type SessionKey = substrate_primitives::AuthorityId;
    /// Indentifier for a chain. 32-bit should be plenty.
    pub type ChainId = u32;
    /// Index of a transaction in the relay chain. 32-bit should be plenty.
    pub type Index = u32;
    /// A hash of some data used by the relay chain.
    pub type Hash = substrate_primitives::H256;
    /// Alias to 512-bit hash when used in the context of a signature on the relay chain.
    /// Equipped with logic for possibly "unsigned" messages.
    pub type Signature =
        runtime_primitives::MaybeUnsigned<runtime_primitives::Ed25519Signature>;
    /// A timestamp: seconds since the unix epoch.
    pub type Timestamp = u64;
    /// The balance of an account.
    /// 128-bits (or 38 significant decimal figures) will allow for 10m currency (10^7) at a resolution
    /// to all for one second's worth of an annualised 50% reward be paid to a unit holder (10^11 unit
    /// denomination), or 10^18 total atomic units, to grow at 50%/year for 51 years (10^9 multiplier)
    /// for an eventual total of 10^27 units (27 significant decimal figures).
    /// We round denomination to 10^12 (12 sdf), and leave the other redundancy at the upper end so
    /// that 32 bits may be multiplied with a balance in 128 bits without worrying about overflow.
    pub type Balance = u128;
    /// Parachain data types.
    pub mod parachain {
        use super::*;
        /// Unique identifier of a parachain.
        #[structural_match]
        #[rustc_copy_clone_marker]
        pub struct Id(u32);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialEq for Id {
            #[inline]
            fn eq(&self, other: &Id) -> bool {
                match *other {
                    Id(ref __self_1_0) =>
                    match *self {
                        Id(ref __self_0_0) => (*__self_0_0) == (*__self_1_0),
                    },
                }
            }
            #[inline]
            fn ne(&self, other: &Id) -> bool {
                match *other {
                    Id(ref __self_1_0) =>
                    match *self {
                        Id(ref __self_0_0) => (*__self_0_0) != (*__self_1_0),
                    },
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::Eq for Id {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_total_eq(&self) -> () {
                { let _: ::std::cmp::AssertParamIsEq<u32>; }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialOrd for Id {
            #[inline]
            fn partial_cmp(&self, other: &Id)
             -> ::std::option::Option<::std::cmp::Ordering> {
                match *other {
                    Id(ref __self_1_0) =>
                    match *self {
                        Id(ref __self_0_0) =>
                        match ::std::cmp::PartialOrd::partial_cmp(&(*__self_0_0),
                                                                  &(*__self_1_0))
                            {
                            ::std::option::Option::Some(::std::cmp::Ordering::Equal)
                            =>
                            ::std::option::Option::Some(::std::cmp::Ordering::Equal),
                            cmp => cmp,
                        },
                    },
                }
            }
            #[inline]
            fn lt(&self, other: &Id) -> bool {
                match *other {
                    Id(ref __self_1_0) =>
                    match *self {
                        Id(ref __self_0_0) => (*__self_0_0) < (*__self_1_0),
                    },
                }
            }
            #[inline]
            fn le(&self, other: &Id) -> bool {
                match *other {
                    Id(ref __self_1_0) =>
                    match *self {
                        Id(ref __self_0_0) => (*__self_0_0) <= (*__self_1_0),
                    },
                }
            }
            #[inline]
            fn gt(&self, other: &Id) -> bool {
                match *other {
                    Id(ref __self_1_0) =>
                    match *self {
                        Id(ref __self_0_0) => (*__self_0_0) > (*__self_1_0),
                    },
                }
            }
            #[inline]
            fn ge(&self, other: &Id) -> bool {
                match *other {
                    Id(ref __self_1_0) =>
                    match *self {
                        Id(ref __self_0_0) => (*__self_0_0) >= (*__self_1_0),
                    },
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::Ord for Id {
            #[inline]
            fn cmp(&self, other: &Id) -> ::std::cmp::Ordering {
                match *other {
                    Id(ref __self_1_0) =>
                    match *self {
                        Id(ref __self_0_0) =>
                        match ::std::cmp::Ord::cmp(&(*__self_0_0),
                                                   &(*__self_1_0)) {
                            ::std::cmp::Ordering::Equal =>
                            ::std::cmp::Ordering::Equal,
                            cmp => cmp,
                        },
                    },
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::hash::Hash for Id {
            fn hash<__H: ::std::hash::Hasher>(&self, state: &mut __H) -> () {
                match *self {
                    Id(ref __self_0_0) => {
                        ::std::hash::Hash::hash(&(*__self_0_0), state)
                    }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::clone::Clone for Id {
            #[inline]
            fn clone(&self) -> Id {
                { let _: ::std::clone::AssertParamIsClone<u32>; *self }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::marker::Copy for Id { }
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_SERIALIZE_FOR_Id: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl _serde::Serialize for Id {
                    fn serialize<__S>(&self, __serializer: __S)
                     -> _serde::export::Result<__S::Ok, __S::Error> where
                     __S: _serde::Serializer {
                        _serde::Serializer::serialize_newtype_struct(__serializer,
                                                                     "Id",
                                                                     &self.0)
                    }
                }
            };
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_DESERIALIZE_FOR_Id: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl <'de> _serde::Deserialize<'de> for Id {
                    fn deserialize<__D>(__deserializer: __D)
                     -> _serde::export::Result<Self, __D::Error> where
                     __D: _serde::Deserializer<'de> {
                        struct __Visitor<'de> {
                            marker: _serde::export::PhantomData<Id>,
                            lifetime: _serde::export::PhantomData<&'de ()>,
                        }
                        impl <'de> _serde::de::Visitor<'de> for __Visitor<'de>
                         {
                            type
                            Value
                            =
                            Id;
                            fn expecting(&self,
                                         __formatter:
                                             &mut _serde::export::Formatter)
                             -> _serde::export::fmt::Result {
                                _serde::export::Formatter::write_str(__formatter,
                                                                     "tuple struct Id")
                            }
                            #[inline]
                            fn visit_newtype_struct<__E>(self, __e: __E)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __E::Error> where
                             __E: _serde::Deserializer<'de> {
                                let __field0: u32 =
                                    match <u32 as
                                              _serde::Deserialize>::deserialize(__e)
                                        {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    };
                                _serde::export::Ok(Id(__field0))
                            }
                            #[inline]
                            fn visit_seq<__A>(self, mut __seq: __A)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __A::Error> where
                             __A: _serde::de::SeqAccess<'de> {
                                let __field0 =
                                    match match _serde::de::SeqAccess::next_element::<u32>(&mut __seq)
                                              {
                                              _serde::export::Ok(__val) =>
                                              __val,
                                              _serde::export::Err(__err) => {
                                                  return _serde::export::Err(__err);
                                              }
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(0usize,
                                                                                                         &"tuple struct Id with 1 element"));
                                        }
                                    };
                                _serde::export::Ok(Id(__field0))
                            }
                        }
                        _serde::Deserializer::deserialize_newtype_struct(__deserializer,
                                                                         "Id",
                                                                         __Visitor{marker:
                                                                                       _serde::export::PhantomData::<Id>,
                                                                                   lifetime:
                                                                                       _serde::export::PhantomData,})
                    }
                }
            };
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::fmt::Debug for Id {
            fn fmt(&self, f: &mut ::std::fmt::Formatter)
             -> ::std::fmt::Result {
                match *self {
                    Id(ref __self_0_0) => {
                        let mut debug_trait_builder = f.debug_tuple("Id");
                        let _ = debug_trait_builder.field(&&(*__self_0_0));
                        debug_trait_builder.finish()
                    }
                }
            }
        }
        impl From<Id> for u32 {
            fn from(x: Id) -> Self { x.0 }
        }
        impl From<u32> for Id {
            fn from(x: u32) -> Self { Id(x) }
        }
        impl Id {
            /// Convert this Id into its inner representation.
            pub fn into_inner(self) -> u32 { self.0 }
        }
        impl Slicable for Id {
            fn decode<I: Input>(input: &mut I) -> Option<Self> {
                u32::decode(input).map(Id)
            }
            fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
                self.0.using_encoded(f)
            }
        }
        /// Identifier for a chain, either one of a number of parachains or the relay chain.
        #[rustc_copy_clone_marker]
        pub enum Chain {

            /// The relay chain.
            Relay,

            /// A parachain of the given index.
            Parachain(Id),
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::marker::Copy for Chain { }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::clone::Clone for Chain {
            #[inline]
            fn clone(&self) -> Chain {
                { let _: ::std::clone::AssertParamIsClone<Id>; *self }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialEq for Chain {
            #[inline]
            fn eq(&self, other: &Chain) -> bool {
                {
                    let __self_vi =
                        unsafe {
                            ::std::intrinsics::discriminant_value(&*self)
                        } as isize;
                    let __arg_1_vi =
                        unsafe {
                            ::std::intrinsics::discriminant_value(&*other)
                        } as isize;
                    if true && __self_vi == __arg_1_vi {
                        match (&*self, &*other) {
                            (&Chain::Parachain(ref __self_0),
                             &Chain::Parachain(ref __arg_1_0)) =>
                            (*__self_0) == (*__arg_1_0),
                            _ => true,
                        }
                    } else { false }
                }
            }
            #[inline]
            fn ne(&self, other: &Chain) -> bool {
                {
                    let __self_vi =
                        unsafe {
                            ::std::intrinsics::discriminant_value(&*self)
                        } as isize;
                    let __arg_1_vi =
                        unsafe {
                            ::std::intrinsics::discriminant_value(&*other)
                        } as isize;
                    if true && __self_vi == __arg_1_vi {
                        match (&*self, &*other) {
                            (&Chain::Parachain(ref __self_0),
                             &Chain::Parachain(ref __arg_1_0)) =>
                            (*__self_0) != (*__arg_1_0),
                            _ => false,
                        }
                    } else { true }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::fmt::Debug for Chain {
            fn fmt(&self, f: &mut ::std::fmt::Formatter)
             -> ::std::fmt::Result {
                match (&*self,) {
                    (&Chain::Relay,) => {
                        let mut debug_trait_builder = f.debug_tuple("Relay");
                        debug_trait_builder.finish()
                    }
                    (&Chain::Parachain(ref __self_0),) => {
                        let mut debug_trait_builder =
                            f.debug_tuple("Parachain");
                        let _ = debug_trait_builder.field(&&(*__self_0));
                        debug_trait_builder.finish()
                    }
                }
            }
        }
        impl Slicable for Chain {
            fn decode<I: Input>(input: &mut I) -> Option<Self> {
                let disc = input.read_byte()?;
                match disc {
                    0 => Some(Chain::Relay),
                    1 => Some(Chain::Parachain(Slicable::decode(input)?)),
                    _ => None,
                }
            }
            fn encode(&self) -> Vec<u8> {
                let mut v = Vec::new();
                match *self {
                    Chain::Relay => { v.push(0); }
                    Chain::Parachain(id) => {
                        v.push(1u8);
                        id.using_encoded(|s| v.extend(s));
                    }
                }
                v
            }
            fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
                f(&self.encode().as_slice())
            }
        }
        /// The duty roster specifying what jobs each validator must do.
        pub struct DutyRoster {
            /// Lookup from validator index to chain on which that validator has a duty to validate.
            pub validator_duty: Vec<Chain>,
            /// Lookup from validator index to chain on which that validator has a duty to guarantee
            /// availability.
            pub guarantor_duty: Vec<Chain>,
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::clone::Clone for DutyRoster {
            #[inline]
            fn clone(&self) -> DutyRoster {
                match *self {
                    DutyRoster {
                    validator_duty: ref __self_0_0,
                    guarantor_duty: ref __self_0_1 } =>
                    DutyRoster{validator_duty:
                                   ::std::clone::Clone::clone(&(*__self_0_0)),
                               guarantor_duty:
                                   ::std::clone::Clone::clone(&(*__self_0_1)),},
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialEq for DutyRoster {
            #[inline]
            fn eq(&self, other: &DutyRoster) -> bool {
                match *other {
                    DutyRoster {
                    validator_duty: ref __self_1_0,
                    guarantor_duty: ref __self_1_1 } =>
                    match *self {
                        DutyRoster {
                        validator_duty: ref __self_0_0,
                        guarantor_duty: ref __self_0_1 } =>
                        (*__self_0_0) == (*__self_1_0) &&
                            (*__self_0_1) == (*__self_1_1),
                    },
                }
            }
            #[inline]
            fn ne(&self, other: &DutyRoster) -> bool {
                match *other {
                    DutyRoster {
                    validator_duty: ref __self_1_0,
                    guarantor_duty: ref __self_1_1 } =>
                    match *self {
                        DutyRoster {
                        validator_duty: ref __self_0_0,
                        guarantor_duty: ref __self_0_1 } =>
                        (*__self_0_0) != (*__self_1_0) ||
                            (*__self_0_1) != (*__self_1_1),
                    },
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::default::Default for DutyRoster {
            #[inline]
            fn default() -> DutyRoster {
                DutyRoster{validator_duty: ::std::default::Default::default(),
                           guarantor_duty:
                               ::std::default::Default::default(),}
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::fmt::Debug for DutyRoster {
            fn fmt(&self, f: &mut ::std::fmt::Formatter)
             -> ::std::fmt::Result {
                match *self {
                    DutyRoster {
                    validator_duty: ref __self_0_0,
                    guarantor_duty: ref __self_0_1 } => {
                        let mut debug_trait_builder =
                            f.debug_struct("DutyRoster");
                        let _ =
                            debug_trait_builder.field("validator_duty",
                                                      &&(*__self_0_0));
                        let _ =
                            debug_trait_builder.field("guarantor_duty",
                                                      &&(*__self_0_1));
                        debug_trait_builder.finish()
                    }
                }
            }
        }
        impl Slicable for DutyRoster {
            fn decode<I: Input>(input: &mut I) -> Option<Self> {
                Some(DutyRoster{validator_duty: Slicable::decode(input)?,
                                guarantor_duty: Slicable::decode(input)?,})
            }
            fn encode(&self) -> Vec<u8> {
                let mut v = Vec::new();
                v.extend(self.validator_duty.encode());
                v.extend(self.guarantor_duty.encode());
                v
            }
            fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
                f(&self.encode().as_slice())
            }
        }
        /// Extrinsic data for a parachain.
        #[serde(rename_all = "camelCase")]
        #[serde(deny_unknown_fields)]
        #[structural_match]
        pub struct Extrinsic;
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialEq for Extrinsic {
            #[inline]
            fn eq(&self, other: &Extrinsic) -> bool {
                match *other {
                    Extrinsic => match *self { Extrinsic => true, },
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::Eq for Extrinsic {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_total_eq(&self) -> () { { } }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::clone::Clone for Extrinsic {
            #[inline]
            fn clone(&self) -> Extrinsic {
                match *self { Extrinsic => Extrinsic, }
            }
        }
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_SERIALIZE_FOR_Extrinsic: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl _serde::Serialize for Extrinsic {
                    fn serialize<__S>(&self, __serializer: __S)
                     -> _serde::export::Result<__S::Ok, __S::Error> where
                     __S: _serde::Serializer {
                        _serde::Serializer::serialize_unit_struct(__serializer,
                                                                  "Extrinsic")
                    }
                }
            };
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_DESERIALIZE_FOR_Extrinsic: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl <'de> _serde::Deserialize<'de> for Extrinsic {
                    fn deserialize<__D>(__deserializer: __D)
                     -> _serde::export::Result<Self, __D::Error> where
                     __D: _serde::Deserializer<'de> {
                        struct __Visitor;
                        impl <'de> _serde::de::Visitor<'de> for __Visitor {
                            type
                            Value
                            =
                            Extrinsic;
                            fn expecting(&self,
                                         __formatter:
                                             &mut _serde::export::Formatter)
                             -> _serde::export::fmt::Result {
                                _serde::export::Formatter::write_str(__formatter,
                                                                     "unit struct Extrinsic")
                            }
                            #[inline]
                            fn visit_unit<__E>(self)
                             -> _serde::export::Result<Self::Value, __E> where
                             __E: _serde::de::Error {
                                _serde::export::Ok(Extrinsic)
                            }
                        }
                        _serde::Deserializer::deserialize_unit_struct(__deserializer,
                                                                      "Extrinsic",
                                                                      __Visitor)
                    }
                }
            };
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::fmt::Debug for Extrinsic {
            fn fmt(&self, f: &mut ::std::fmt::Formatter)
             -> ::std::fmt::Result {
                match *self {
                    Extrinsic => {
                        let mut debug_trait_builder =
                            f.debug_tuple("Extrinsic");
                        debug_trait_builder.finish()
                    }
                }
            }
        }
        /// Candidate parachain block.
        ///
        /// https://github.com/w3f/polkadot-spec/blob/master/spec.md#candidate-para-chain-block
        #[serde(rename_all = "camelCase")]
        #[serde(deny_unknown_fields)]
        #[structural_match]
        pub struct Candidate {
            /// The ID of the parachain this is a proposal for.
            pub parachain_index: Id,
            /// Collator's signature
            pub collator_signature: runtime_primitives::Ed25519Signature,
            /// Unprocessed ingress queue.
            ///
            /// Ordered by parachain ID and block number.
            pub unprocessed_ingress: ConsolidatedIngress,
            /// Block data
            pub block: BlockData,
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialEq for Candidate {
            #[inline]
            fn eq(&self, other: &Candidate) -> bool {
                match *other {
                    Candidate {
                    parachain_index: ref __self_1_0,
                    collator_signature: ref __self_1_1,
                    unprocessed_ingress: ref __self_1_2,
                    block: ref __self_1_3 } =>
                    match *self {
                        Candidate {
                        parachain_index: ref __self_0_0,
                        collator_signature: ref __self_0_1,
                        unprocessed_ingress: ref __self_0_2,
                        block: ref __self_0_3 } =>
                        (*__self_0_0) == (*__self_1_0) &&
                            (*__self_0_1) == (*__self_1_1) &&
                            (*__self_0_2) == (*__self_1_2) &&
                            (*__self_0_3) == (*__self_1_3),
                    },
                }
            }
            #[inline]
            fn ne(&self, other: &Candidate) -> bool {
                match *other {
                    Candidate {
                    parachain_index: ref __self_1_0,
                    collator_signature: ref __self_1_1,
                    unprocessed_ingress: ref __self_1_2,
                    block: ref __self_1_3 } =>
                    match *self {
                        Candidate {
                        parachain_index: ref __self_0_0,
                        collator_signature: ref __self_0_1,
                        unprocessed_ingress: ref __self_0_2,
                        block: ref __self_0_3 } =>
                        (*__self_0_0) != (*__self_1_0) ||
                            (*__self_0_1) != (*__self_1_1) ||
                            (*__self_0_2) != (*__self_1_2) ||
                            (*__self_0_3) != (*__self_1_3),
                    },
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::Eq for Candidate {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::std::cmp::AssertParamIsEq<Id>;
                    let _:
                            ::std::cmp::AssertParamIsEq<runtime_primitives::Ed25519Signature>;
                    let _: ::std::cmp::AssertParamIsEq<ConsolidatedIngress>;
                    let _: ::std::cmp::AssertParamIsEq<BlockData>;
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::clone::Clone for Candidate {
            #[inline]
            fn clone(&self) -> Candidate {
                match *self {
                    Candidate {
                    parachain_index: ref __self_0_0,
                    collator_signature: ref __self_0_1,
                    unprocessed_ingress: ref __self_0_2,
                    block: ref __self_0_3 } =>
                    Candidate{parachain_index:
                                  ::std::clone::Clone::clone(&(*__self_0_0)),
                              collator_signature:
                                  ::std::clone::Clone::clone(&(*__self_0_1)),
                              unprocessed_ingress:
                                  ::std::clone::Clone::clone(&(*__self_0_2)),
                              block:
                                  ::std::clone::Clone::clone(&(*__self_0_3)),},
                }
            }
        }
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_SERIALIZE_FOR_Candidate: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl _serde::Serialize for Candidate {
                    fn serialize<__S>(&self, __serializer: __S)
                     -> _serde::export::Result<__S::Ok, __S::Error> where
                     __S: _serde::Serializer {
                        let mut __serde_state =
                            match _serde::Serializer::serialize_struct(__serializer,
                                                                       "Candidate",
                                                                       0 + 1 +
                                                                           1 +
                                                                           1 +
                                                                           1)
                                {
                                _serde::export::Ok(__val) => __val,
                                _serde::export::Err(__err) => {
                                    return _serde::export::Err(__err);
                                }
                            };
                        match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                            "parachainIndex",
                                                                            &self.parachain_index)
                            {
                            _serde::export::Ok(__val) => __val,
                            _serde::export::Err(__err) => {
                                return _serde::export::Err(__err);
                            }
                        };
                        match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                            "collatorSignature",
                                                                            &self.collator_signature)
                            {
                            _serde::export::Ok(__val) => __val,
                            _serde::export::Err(__err) => {
                                return _serde::export::Err(__err);
                            }
                        };
                        match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                            "unprocessedIngress",
                                                                            &self.unprocessed_ingress)
                            {
                            _serde::export::Ok(__val) => __val,
                            _serde::export::Err(__err) => {
                                return _serde::export::Err(__err);
                            }
                        };
                        match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                            "block",
                                                                            &self.block)
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
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_DESERIALIZE_FOR_Candidate: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl <'de> _serde::Deserialize<'de> for Candidate {
                    fn deserialize<__D>(__deserializer: __D)
                     -> _serde::export::Result<Self, __D::Error> where
                     __D: _serde::Deserializer<'de> {
                        #[allow(non_camel_case_types)]
                        enum __Field {
                            __field0,
                            __field1,
                            __field2,
                            __field3,
                        }
                        struct __FieldVisitor;
                        impl <'de> _serde::de::Visitor<'de> for __FieldVisitor
                         {
                            type
                            Value
                            =
                            __Field;
                            fn expecting(&self,
                                         __formatter:
                                             &mut _serde::export::Formatter)
                             -> _serde::export::fmt::Result {
                                _serde::export::Formatter::write_str(__formatter,
                                                                     "field identifier")
                            }
                            fn visit_u64<__E>(self, __value: u64)
                             -> _serde::export::Result<Self::Value, __E> where
                             __E: _serde::de::Error {
                                match __value {
                                    0u64 =>
                                    _serde::export::Ok(__Field::__field0),
                                    1u64 =>
                                    _serde::export::Ok(__Field::__field1),
                                    2u64 =>
                                    _serde::export::Ok(__Field::__field2),
                                    3u64 =>
                                    _serde::export::Ok(__Field::__field3),
                                    _ =>
                                    _serde::export::Err(_serde::de::Error::invalid_value(_serde::de::Unexpected::Unsigned(__value),
                                                                                         &"field index 0 <= i < 4")),
                                }
                            }
                            fn visit_str<__E>(self, __value: &str)
                             -> _serde::export::Result<Self::Value, __E> where
                             __E: _serde::de::Error {
                                match __value {
                                    "parachainIndex" =>
                                    _serde::export::Ok(__Field::__field0),
                                    "collatorSignature" =>
                                    _serde::export::Ok(__Field::__field1),
                                    "unprocessedIngress" =>
                                    _serde::export::Ok(__Field::__field2),
                                    "block" =>
                                    _serde::export::Ok(__Field::__field3),
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
                                    b"parachainIndex" =>
                                    _serde::export::Ok(__Field::__field0),
                                    b"collatorSignature" =>
                                    _serde::export::Ok(__Field::__field1),
                                    b"unprocessedIngress" =>
                                    _serde::export::Ok(__Field::__field2),
                                    b"block" =>
                                    _serde::export::Ok(__Field::__field3),
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
                            marker: _serde::export::PhantomData<Candidate>,
                            lifetime: _serde::export::PhantomData<&'de ()>,
                        }
                        impl <'de> _serde::de::Visitor<'de> for __Visitor<'de>
                         {
                            type
                            Value
                            =
                            Candidate;
                            fn expecting(&self,
                                         __formatter:
                                             &mut _serde::export::Formatter)
                             -> _serde::export::fmt::Result {
                                _serde::export::Formatter::write_str(__formatter,
                                                                     "struct Candidate")
                            }
                            #[inline]
                            fn visit_seq<__A>(self, mut __seq: __A)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __A::Error> where
                             __A: _serde::de::SeqAccess<'de> {
                                let __field0 =
                                    match match _serde::de::SeqAccess::next_element::<Id>(&mut __seq)
                                              {
                                              _serde::export::Ok(__val) =>
                                              __val,
                                              _serde::export::Err(__err) => {
                                                  return _serde::export::Err(__err);
                                              }
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(0usize,
                                                                                                         &"struct Candidate with 4 elements"));
                                        }
                                    };
                                let __field1 =
                                    match match _serde::de::SeqAccess::next_element::<runtime_primitives::Ed25519Signature>(&mut __seq)
                                              {
                                              _serde::export::Ok(__val) =>
                                              __val,
                                              _serde::export::Err(__err) => {
                                                  return _serde::export::Err(__err);
                                              }
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(1usize,
                                                                                                         &"struct Candidate with 4 elements"));
                                        }
                                    };
                                let __field2 =
                                    match match _serde::de::SeqAccess::next_element::<ConsolidatedIngress>(&mut __seq)
                                              {
                                              _serde::export::Ok(__val) =>
                                              __val,
                                              _serde::export::Err(__err) => {
                                                  return _serde::export::Err(__err);
                                              }
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(2usize,
                                                                                                         &"struct Candidate with 4 elements"));
                                        }
                                    };
                                let __field3 =
                                    match match _serde::de::SeqAccess::next_element::<BlockData>(&mut __seq)
                                              {
                                              _serde::export::Ok(__val) =>
                                              __val,
                                              _serde::export::Err(__err) => {
                                                  return _serde::export::Err(__err);
                                              }
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(3usize,
                                                                                                         &"struct Candidate with 4 elements"));
                                        }
                                    };
                                _serde::export::Ok(Candidate{parachain_index:
                                                                 __field0,
                                                             collator_signature:
                                                                 __field1,
                                                             unprocessed_ingress:
                                                                 __field2,
                                                             block:
                                                                 __field3,})
                            }
                            #[inline]
                            fn visit_map<__A>(self, mut __map: __A)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __A::Error> where
                             __A: _serde::de::MapAccess<'de> {
                                let mut __field0: _serde::export::Option<Id> =
                                    _serde::export::None;
                                let mut __field1:
                                        _serde::export::Option<runtime_primitives::Ed25519Signature> =
                                    _serde::export::None;
                                let mut __field2:
                                        _serde::export::Option<ConsolidatedIngress> =
                                    _serde::export::None;
                                let mut __field3:
                                        _serde::export::Option<BlockData> =
                                    _serde::export::None;
                                while let _serde::export::Some(__key) =
                                          match _serde::de::MapAccess::next_key::<__Field>(&mut __map)
                                              {
                                              _serde::export::Ok(__val) =>
                                              __val,
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
                                                                               _serde::de::Error>::duplicate_field("parachainIndex"));
                                            }
                                            __field0 =
                                                _serde::export::Some(match _serde::de::MapAccess::next_value::<Id>(&mut __map)
                                                                         {
                                                                         _serde::export::Ok(__val)
                                                                         =>
                                                                         __val,
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
                                                                               _serde::de::Error>::duplicate_field("collatorSignature"));
                                            }
                                            __field1 =
                                                _serde::export::Some(match _serde::de::MapAccess::next_value::<runtime_primitives::Ed25519Signature>(&mut __map)
                                                                         {
                                                                         _serde::export::Ok(__val)
                                                                         =>
                                                                         __val,
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
                                                                               _serde::de::Error>::duplicate_field("unprocessedIngress"));
                                            }
                                            __field2 =
                                                _serde::export::Some(match _serde::de::MapAccess::next_value::<ConsolidatedIngress>(&mut __map)
                                                                         {
                                                                         _serde::export::Ok(__val)
                                                                         =>
                                                                         __val,
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
                                                                               _serde::de::Error>::duplicate_field("block"));
                                            }
                                            __field3 =
                                                _serde::export::Some(match _serde::de::MapAccess::next_value::<BlockData>(&mut __map)
                                                                         {
                                                                         _serde::export::Ok(__val)
                                                                         =>
                                                                         __val,
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
                                        _serde::export::Some(__field0) =>
                                        __field0,
                                        _serde::export::None =>
                                        match _serde::private::de::missing_field("parachainIndex")
                                            {
                                            _serde::export::Ok(__val) =>
                                            __val,
                                            _serde::export::Err(__err) => {
                                                return _serde::export::Err(__err);
                                            }
                                        },
                                    };
                                let __field1 =
                                    match __field1 {
                                        _serde::export::Some(__field1) =>
                                        __field1,
                                        _serde::export::None =>
                                        match _serde::private::de::missing_field("collatorSignature")
                                            {
                                            _serde::export::Ok(__val) =>
                                            __val,
                                            _serde::export::Err(__err) => {
                                                return _serde::export::Err(__err);
                                            }
                                        },
                                    };
                                let __field2 =
                                    match __field2 {
                                        _serde::export::Some(__field2) =>
                                        __field2,
                                        _serde::export::None =>
                                        match _serde::private::de::missing_field("unprocessedIngress")
                                            {
                                            _serde::export::Ok(__val) =>
                                            __val,
                                            _serde::export::Err(__err) => {
                                                return _serde::export::Err(__err);
                                            }
                                        },
                                    };
                                let __field3 =
                                    match __field3 {
                                        _serde::export::Some(__field3) =>
                                        __field3,
                                        _serde::export::None =>
                                        match _serde::private::de::missing_field("block")
                                            {
                                            _serde::export::Ok(__val) =>
                                            __val,
                                            _serde::export::Err(__err) => {
                                                return _serde::export::Err(__err);
                                            }
                                        },
                                    };
                                _serde::export::Ok(Candidate{parachain_index:
                                                                 __field0,
                                                             collator_signature:
                                                                 __field1,
                                                             unprocessed_ingress:
                                                                 __field2,
                                                             block:
                                                                 __field3,})
                            }
                        }
                        const FIELDS: &'static [&'static str] =
                            &["parachainIndex", "collatorSignature",
                              "unprocessedIngress", "block"];
                        _serde::Deserializer::deserialize_struct(__deserializer,
                                                                 "Candidate",
                                                                 FIELDS,
                                                                 __Visitor{marker:
                                                                               _serde::export::PhantomData::<Candidate>,
                                                                           lifetime:
                                                                               _serde::export::PhantomData,})
                    }
                }
            };
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::fmt::Debug for Candidate {
            fn fmt(&self, f: &mut ::std::fmt::Formatter)
             -> ::std::fmt::Result {
                match *self {
                    Candidate {
                    parachain_index: ref __self_0_0,
                    collator_signature: ref __self_0_1,
                    unprocessed_ingress: ref __self_0_2,
                    block: ref __self_0_3 } => {
                        let mut debug_trait_builder =
                            f.debug_struct("Candidate");
                        let _ =
                            debug_trait_builder.field("parachain_index",
                                                      &&(*__self_0_0));
                        let _ =
                            debug_trait_builder.field("collator_signature",
                                                      &&(*__self_0_1));
                        let _ =
                            debug_trait_builder.field("unprocessed_ingress",
                                                      &&(*__self_0_2));
                        let _ =
                            debug_trait_builder.field("block",
                                                      &&(*__self_0_3));
                        debug_trait_builder.finish()
                    }
                }
            }
        }
        /// Candidate receipt type.
        #[serde(rename_all = "camelCase")]
        #[serde(deny_unknown_fields)]
        #[structural_match]
        pub struct CandidateReceipt {
            /// The ID of the parachain this is a candidate for.
            pub parachain_index: Id,
            /// The collator's relay-chain account ID
            pub collator: super::AccountId,
            /// The head-data
            pub head_data: HeadData,
            /// Balance uploads to the relay chain.
            pub balance_uploads: Vec<(super::AccountId, u64)>,
            /// Egress queue roots.
            pub egress_queue_roots: Vec<(Id, Hash)>,
            /// Fees paid from the chain to the relay chain validators
            pub fees: u64,
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialEq for CandidateReceipt {
            #[inline]
            fn eq(&self, other: &CandidateReceipt) -> bool {
                match *other {
                    CandidateReceipt {
                    parachain_index: ref __self_1_0,
                    collator: ref __self_1_1,
                    head_data: ref __self_1_2,
                    balance_uploads: ref __self_1_3,
                    egress_queue_roots: ref __self_1_4,
                    fees: ref __self_1_5 } =>
                    match *self {
                        CandidateReceipt {
                        parachain_index: ref __self_0_0,
                        collator: ref __self_0_1,
                        head_data: ref __self_0_2,
                        balance_uploads: ref __self_0_3,
                        egress_queue_roots: ref __self_0_4,
                        fees: ref __self_0_5 } =>
                        (*__self_0_0) == (*__self_1_0) &&
                            (*__self_0_1) == (*__self_1_1) &&
                            (*__self_0_2) == (*__self_1_2) &&
                            (*__self_0_3) == (*__self_1_3) &&
                            (*__self_0_4) == (*__self_1_4) &&
                            (*__self_0_5) == (*__self_1_5),
                    },
                }
            }
            #[inline]
            fn ne(&self, other: &CandidateReceipt) -> bool {
                match *other {
                    CandidateReceipt {
                    parachain_index: ref __self_1_0,
                    collator: ref __self_1_1,
                    head_data: ref __self_1_2,
                    balance_uploads: ref __self_1_3,
                    egress_queue_roots: ref __self_1_4,
                    fees: ref __self_1_5 } =>
                    match *self {
                        CandidateReceipt {
                        parachain_index: ref __self_0_0,
                        collator: ref __self_0_1,
                        head_data: ref __self_0_2,
                        balance_uploads: ref __self_0_3,
                        egress_queue_roots: ref __self_0_4,
                        fees: ref __self_0_5 } =>
                        (*__self_0_0) != (*__self_1_0) ||
                            (*__self_0_1) != (*__self_1_1) ||
                            (*__self_0_2) != (*__self_1_2) ||
                            (*__self_0_3) != (*__self_1_3) ||
                            (*__self_0_4) != (*__self_1_4) ||
                            (*__self_0_5) != (*__self_1_5),
                    },
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::Eq for CandidateReceipt {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::std::cmp::AssertParamIsEq<Id>;
                    let _: ::std::cmp::AssertParamIsEq<super::AccountId>;
                    let _: ::std::cmp::AssertParamIsEq<HeadData>;
                    let _:
                            ::std::cmp::AssertParamIsEq<Vec<(super::AccountId,
                                                             u64)>>;
                    let _: ::std::cmp::AssertParamIsEq<Vec<(Id, Hash)>>;
                    let _: ::std::cmp::AssertParamIsEq<u64>;
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::clone::Clone for CandidateReceipt {
            #[inline]
            fn clone(&self) -> CandidateReceipt {
                match *self {
                    CandidateReceipt {
                    parachain_index: ref __self_0_0,
                    collator: ref __self_0_1,
                    head_data: ref __self_0_2,
                    balance_uploads: ref __self_0_3,
                    egress_queue_roots: ref __self_0_4,
                    fees: ref __self_0_5 } =>
                    CandidateReceipt{parachain_index:
                                         ::std::clone::Clone::clone(&(*__self_0_0)),
                                     collator:
                                         ::std::clone::Clone::clone(&(*__self_0_1)),
                                     head_data:
                                         ::std::clone::Clone::clone(&(*__self_0_2)),
                                     balance_uploads:
                                         ::std::clone::Clone::clone(&(*__self_0_3)),
                                     egress_queue_roots:
                                         ::std::clone::Clone::clone(&(*__self_0_4)),
                                     fees:
                                         ::std::clone::Clone::clone(&(*__self_0_5)),},
                }
            }
        }
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_SERIALIZE_FOR_CandidateReceipt: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl _serde::Serialize for CandidateReceipt {
                    fn serialize<__S>(&self, __serializer: __S)
                     -> _serde::export::Result<__S::Ok, __S::Error> where
                     __S: _serde::Serializer {
                        let mut __serde_state =
                            match _serde::Serializer::serialize_struct(__serializer,
                                                                       "CandidateReceipt",
                                                                       0 + 1 +
                                                                           1 +
                                                                           1 +
                                                                           1 +
                                                                           1 +
                                                                           1)
                                {
                                _serde::export::Ok(__val) => __val,
                                _serde::export::Err(__err) => {
                                    return _serde::export::Err(__err);
                                }
                            };
                        match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                            "parachainIndex",
                                                                            &self.parachain_index)
                            {
                            _serde::export::Ok(__val) => __val,
                            _serde::export::Err(__err) => {
                                return _serde::export::Err(__err);
                            }
                        };
                        match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                            "collator",
                                                                            &self.collator)
                            {
                            _serde::export::Ok(__val) => __val,
                            _serde::export::Err(__err) => {
                                return _serde::export::Err(__err);
                            }
                        };
                        match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                            "headData",
                                                                            &self.head_data)
                            {
                            _serde::export::Ok(__val) => __val,
                            _serde::export::Err(__err) => {
                                return _serde::export::Err(__err);
                            }
                        };
                        match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                            "balanceUploads",
                                                                            &self.balance_uploads)
                            {
                            _serde::export::Ok(__val) => __val,
                            _serde::export::Err(__err) => {
                                return _serde::export::Err(__err);
                            }
                        };
                        match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                            "egressQueueRoots",
                                                                            &self.egress_queue_roots)
                            {
                            _serde::export::Ok(__val) => __val,
                            _serde::export::Err(__err) => {
                                return _serde::export::Err(__err);
                            }
                        };
                        match _serde::ser::SerializeStruct::serialize_field(&mut __serde_state,
                                                                            "fees",
                                                                            &self.fees)
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
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_DESERIALIZE_FOR_CandidateReceipt: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl <'de> _serde::Deserialize<'de> for CandidateReceipt {
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
                        }
                        struct __FieldVisitor;
                        impl <'de> _serde::de::Visitor<'de> for __FieldVisitor
                         {
                            type
                            Value
                            =
                            __Field;
                            fn expecting(&self,
                                         __formatter:
                                             &mut _serde::export::Formatter)
                             -> _serde::export::fmt::Result {
                                _serde::export::Formatter::write_str(__formatter,
                                                                     "field identifier")
                            }
                            fn visit_u64<__E>(self, __value: u64)
                             -> _serde::export::Result<Self::Value, __E> where
                             __E: _serde::de::Error {
                                match __value {
                                    0u64 =>
                                    _serde::export::Ok(__Field::__field0),
                                    1u64 =>
                                    _serde::export::Ok(__Field::__field1),
                                    2u64 =>
                                    _serde::export::Ok(__Field::__field2),
                                    3u64 =>
                                    _serde::export::Ok(__Field::__field3),
                                    4u64 =>
                                    _serde::export::Ok(__Field::__field4),
                                    5u64 =>
                                    _serde::export::Ok(__Field::__field5),
                                    _ =>
                                    _serde::export::Err(_serde::de::Error::invalid_value(_serde::de::Unexpected::Unsigned(__value),
                                                                                         &"field index 0 <= i < 6")),
                                }
                            }
                            fn visit_str<__E>(self, __value: &str)
                             -> _serde::export::Result<Self::Value, __E> where
                             __E: _serde::de::Error {
                                match __value {
                                    "parachainIndex" =>
                                    _serde::export::Ok(__Field::__field0),
                                    "collator" =>
                                    _serde::export::Ok(__Field::__field1),
                                    "headData" =>
                                    _serde::export::Ok(__Field::__field2),
                                    "balanceUploads" =>
                                    _serde::export::Ok(__Field::__field3),
                                    "egressQueueRoots" =>
                                    _serde::export::Ok(__Field::__field4),
                                    "fees" =>
                                    _serde::export::Ok(__Field::__field5),
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
                                    b"parachainIndex" =>
                                    _serde::export::Ok(__Field::__field0),
                                    b"collator" =>
                                    _serde::export::Ok(__Field::__field1),
                                    b"headData" =>
                                    _serde::export::Ok(__Field::__field2),
                                    b"balanceUploads" =>
                                    _serde::export::Ok(__Field::__field3),
                                    b"egressQueueRoots" =>
                                    _serde::export::Ok(__Field::__field4),
                                    b"fees" =>
                                    _serde::export::Ok(__Field::__field5),
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
                            marker: _serde::export::PhantomData<CandidateReceipt>,
                            lifetime: _serde::export::PhantomData<&'de ()>,
                        }
                        impl <'de> _serde::de::Visitor<'de> for __Visitor<'de>
                         {
                            type
                            Value
                            =
                            CandidateReceipt;
                            fn expecting(&self,
                                         __formatter:
                                             &mut _serde::export::Formatter)
                             -> _serde::export::fmt::Result {
                                _serde::export::Formatter::write_str(__formatter,
                                                                     "struct CandidateReceipt")
                            }
                            #[inline]
                            fn visit_seq<__A>(self, mut __seq: __A)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __A::Error> where
                             __A: _serde::de::SeqAccess<'de> {
                                let __field0 =
                                    match match _serde::de::SeqAccess::next_element::<Id>(&mut __seq)
                                              {
                                              _serde::export::Ok(__val) =>
                                              __val,
                                              _serde::export::Err(__err) => {
                                                  return _serde::export::Err(__err);
                                              }
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(0usize,
                                                                                                         &"struct CandidateReceipt with 6 elements"));
                                        }
                                    };
                                let __field1 =
                                    match match _serde::de::SeqAccess::next_element::<super::AccountId>(&mut __seq)
                                              {
                                              _serde::export::Ok(__val) =>
                                              __val,
                                              _serde::export::Err(__err) => {
                                                  return _serde::export::Err(__err);
                                              }
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(1usize,
                                                                                                         &"struct CandidateReceipt with 6 elements"));
                                        }
                                    };
                                let __field2 =
                                    match match _serde::de::SeqAccess::next_element::<HeadData>(&mut __seq)
                                              {
                                              _serde::export::Ok(__val) =>
                                              __val,
                                              _serde::export::Err(__err) => {
                                                  return _serde::export::Err(__err);
                                              }
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(2usize,
                                                                                                         &"struct CandidateReceipt with 6 elements"));
                                        }
                                    };
                                let __field3 =
                                    match match _serde::de::SeqAccess::next_element::<Vec<(super::AccountId,
                                                                                           u64)>>(&mut __seq)
                                              {
                                              _serde::export::Ok(__val) =>
                                              __val,
                                              _serde::export::Err(__err) => {
                                                  return _serde::export::Err(__err);
                                              }
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(3usize,
                                                                                                         &"struct CandidateReceipt with 6 elements"));
                                        }
                                    };
                                let __field4 =
                                    match match _serde::de::SeqAccess::next_element::<Vec<(Id,
                                                                                           Hash)>>(&mut __seq)
                                              {
                                              _serde::export::Ok(__val) =>
                                              __val,
                                              _serde::export::Err(__err) => {
                                                  return _serde::export::Err(__err);
                                              }
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(4usize,
                                                                                                         &"struct CandidateReceipt with 6 elements"));
                                        }
                                    };
                                let __field5 =
                                    match match _serde::de::SeqAccess::next_element::<u64>(&mut __seq)
                                              {
                                              _serde::export::Ok(__val) =>
                                              __val,
                                              _serde::export::Err(__err) => {
                                                  return _serde::export::Err(__err);
                                              }
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(5usize,
                                                                                                         &"struct CandidateReceipt with 6 elements"));
                                        }
                                    };
                                _serde::export::Ok(CandidateReceipt{parachain_index:
                                                                        __field0,
                                                                    collator:
                                                                        __field1,
                                                                    head_data:
                                                                        __field2,
                                                                    balance_uploads:
                                                                        __field3,
                                                                    egress_queue_roots:
                                                                        __field4,
                                                                    fees:
                                                                        __field5,})
                            }
                            #[inline]
                            fn visit_map<__A>(self, mut __map: __A)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __A::Error> where
                             __A: _serde::de::MapAccess<'de> {
                                let mut __field0: _serde::export::Option<Id> =
                                    _serde::export::None;
                                let mut __field1:
                                        _serde::export::Option<super::AccountId> =
                                    _serde::export::None;
                                let mut __field2:
                                        _serde::export::Option<HeadData> =
                                    _serde::export::None;
                                let mut __field3:
                                        _serde::export::Option<Vec<(super::AccountId,
                                                                    u64)>> =
                                    _serde::export::None;
                                let mut __field4:
                                        _serde::export::Option<Vec<(Id,
                                                                    Hash)>> =
                                    _serde::export::None;
                                let mut __field5:
                                        _serde::export::Option<u64> =
                                    _serde::export::None;
                                while let _serde::export::Some(__key) =
                                          match _serde::de::MapAccess::next_key::<__Field>(&mut __map)
                                              {
                                              _serde::export::Ok(__val) =>
                                              __val,
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
                                                                               _serde::de::Error>::duplicate_field("parachainIndex"));
                                            }
                                            __field0 =
                                                _serde::export::Some(match _serde::de::MapAccess::next_value::<Id>(&mut __map)
                                                                         {
                                                                         _serde::export::Ok(__val)
                                                                         =>
                                                                         __val,
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
                                                                               _serde::de::Error>::duplicate_field("collator"));
                                            }
                                            __field1 =
                                                _serde::export::Some(match _serde::de::MapAccess::next_value::<super::AccountId>(&mut __map)
                                                                         {
                                                                         _serde::export::Ok(__val)
                                                                         =>
                                                                         __val,
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
                                                                               _serde::de::Error>::duplicate_field("headData"));
                                            }
                                            __field2 =
                                                _serde::export::Some(match _serde::de::MapAccess::next_value::<HeadData>(&mut __map)
                                                                         {
                                                                         _serde::export::Ok(__val)
                                                                         =>
                                                                         __val,
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
                                                                               _serde::de::Error>::duplicate_field("balanceUploads"));
                                            }
                                            __field3 =
                                                _serde::export::Some(match _serde::de::MapAccess::next_value::<Vec<(super::AccountId,
                                                                                                                    u64)>>(&mut __map)
                                                                         {
                                                                         _serde::export::Ok(__val)
                                                                         =>
                                                                         __val,
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
                                                                               _serde::de::Error>::duplicate_field("egressQueueRoots"));
                                            }
                                            __field4 =
                                                _serde::export::Some(match _serde::de::MapAccess::next_value::<Vec<(Id,
                                                                                                                    Hash)>>(&mut __map)
                                                                         {
                                                                         _serde::export::Ok(__val)
                                                                         =>
                                                                         __val,
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
                                                                               _serde::de::Error>::duplicate_field("fees"));
                                            }
                                            __field5 =
                                                _serde::export::Some(match _serde::de::MapAccess::next_value::<u64>(&mut __map)
                                                                         {
                                                                         _serde::export::Ok(__val)
                                                                         =>
                                                                         __val,
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
                                        _serde::export::Some(__field0) =>
                                        __field0,
                                        _serde::export::None =>
                                        match _serde::private::de::missing_field("parachainIndex")
                                            {
                                            _serde::export::Ok(__val) =>
                                            __val,
                                            _serde::export::Err(__err) => {
                                                return _serde::export::Err(__err);
                                            }
                                        },
                                    };
                                let __field1 =
                                    match __field1 {
                                        _serde::export::Some(__field1) =>
                                        __field1,
                                        _serde::export::None =>
                                        match _serde::private::de::missing_field("collator")
                                            {
                                            _serde::export::Ok(__val) =>
                                            __val,
                                            _serde::export::Err(__err) => {
                                                return _serde::export::Err(__err);
                                            }
                                        },
                                    };
                                let __field2 =
                                    match __field2 {
                                        _serde::export::Some(__field2) =>
                                        __field2,
                                        _serde::export::None =>
                                        match _serde::private::de::missing_field("headData")
                                            {
                                            _serde::export::Ok(__val) =>
                                            __val,
                                            _serde::export::Err(__err) => {
                                                return _serde::export::Err(__err);
                                            }
                                        },
                                    };
                                let __field3 =
                                    match __field3 {
                                        _serde::export::Some(__field3) =>
                                        __field3,
                                        _serde::export::None =>
                                        match _serde::private::de::missing_field("balanceUploads")
                                            {
                                            _serde::export::Ok(__val) =>
                                            __val,
                                            _serde::export::Err(__err) => {
                                                return _serde::export::Err(__err);
                                            }
                                        },
                                    };
                                let __field4 =
                                    match __field4 {
                                        _serde::export::Some(__field4) =>
                                        __field4,
                                        _serde::export::None =>
                                        match _serde::private::de::missing_field("egressQueueRoots")
                                            {
                                            _serde::export::Ok(__val) =>
                                            __val,
                                            _serde::export::Err(__err) => {
                                                return _serde::export::Err(__err);
                                            }
                                        },
                                    };
                                let __field5 =
                                    match __field5 {
                                        _serde::export::Some(__field5) =>
                                        __field5,
                                        _serde::export::None =>
                                        match _serde::private::de::missing_field("fees")
                                            {
                                            _serde::export::Ok(__val) =>
                                            __val,
                                            _serde::export::Err(__err) => {
                                                return _serde::export::Err(__err);
                                            }
                                        },
                                    };
                                _serde::export::Ok(CandidateReceipt{parachain_index:
                                                                        __field0,
                                                                    collator:
                                                                        __field1,
                                                                    head_data:
                                                                        __field2,
                                                                    balance_uploads:
                                                                        __field3,
                                                                    egress_queue_roots:
                                                                        __field4,
                                                                    fees:
                                                                        __field5,})
                            }
                        }
                        const FIELDS: &'static [&'static str] =
                            &["parachainIndex", "collator", "headData",
                              "balanceUploads", "egressQueueRoots", "fees"];
                        _serde::Deserializer::deserialize_struct(__deserializer,
                                                                 "CandidateReceipt",
                                                                 FIELDS,
                                                                 __Visitor{marker:
                                                                               _serde::export::PhantomData::<CandidateReceipt>,
                                                                           lifetime:
                                                                               _serde::export::PhantomData,})
                    }
                }
            };
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::fmt::Debug for CandidateReceipt {
            fn fmt(&self, f: &mut ::std::fmt::Formatter)
             -> ::std::fmt::Result {
                match *self {
                    CandidateReceipt {
                    parachain_index: ref __self_0_0,
                    collator: ref __self_0_1,
                    head_data: ref __self_0_2,
                    balance_uploads: ref __self_0_3,
                    egress_queue_roots: ref __self_0_4,
                    fees: ref __self_0_5 } => {
                        let mut debug_trait_builder =
                            f.debug_struct("CandidateReceipt");
                        let _ =
                            debug_trait_builder.field("parachain_index",
                                                      &&(*__self_0_0));
                        let _ =
                            debug_trait_builder.field("collator",
                                                      &&(*__self_0_1));
                        let _ =
                            debug_trait_builder.field("head_data",
                                                      &&(*__self_0_2));
                        let _ =
                            debug_trait_builder.field("balance_uploads",
                                                      &&(*__self_0_3));
                        let _ =
                            debug_trait_builder.field("egress_queue_roots",
                                                      &&(*__self_0_4));
                        let _ =
                            debug_trait_builder.field("fees",
                                                      &&(*__self_0_5));
                        debug_trait_builder.finish()
                    }
                }
            }
        }
        impl Slicable for CandidateReceipt {
            fn encode(&self) -> Vec<u8> {
                let mut v = Vec::new();
                self.parachain_index.using_encoded(|s| v.extend(s));
                self.collator.using_encoded(|s| v.extend(s));
                self.head_data.0.using_encoded(|s| v.extend(s));
                self.balance_uploads.using_encoded(|s| v.extend(s));
                self.egress_queue_roots.using_encoded(|s| v.extend(s));
                self.fees.using_encoded(|s| v.extend(s));
                v
            }
            fn decode<I: Input>(input: &mut I) -> Option<Self> {
                Some(CandidateReceipt{parachain_index:
                                          Slicable::decode(input)?,
                                      collator: Slicable::decode(input)?,
                                      head_data:
                                          Slicable::decode(input).map(HeadData)?,
                                      balance_uploads:
                                          Slicable::decode(input)?,
                                      egress_queue_roots:
                                          Slicable::decode(input)?,
                                      fees: Slicable::decode(input)?,})
            }
        }
        impl CandidateReceipt {
            /// Get the blake2_256 hash
            #[cfg(feature = "std")]
            pub fn hash(&self) -> Hash {
                use runtime_primitives::traits::Hashing;
                BlakeTwo256::hash_of(self)
            }
        }
        impl PartialOrd for CandidateReceipt {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for CandidateReceipt {
            fn cmp(&self, other: &Self) -> Ordering {
                self.parachain_index.cmp(&other.parachain_index).then_with(||
                                                                               self.head_data.cmp(&other.head_data))
            }
        }
        /// Parachain ingress queue message.
        #[structural_match]
        pub struct Message(
                           #[serde(with = "bytes")]
                           pub Vec<u8>);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialEq for Message {
            #[inline]
            fn eq(&self, other: &Message) -> bool {
                match *other {
                    Message(ref __self_1_0) =>
                    match *self {
                        Message(ref __self_0_0) =>
                        (*__self_0_0) == (*__self_1_0),
                    },
                }
            }
            #[inline]
            fn ne(&self, other: &Message) -> bool {
                match *other {
                    Message(ref __self_1_0) =>
                    match *self {
                        Message(ref __self_0_0) =>
                        (*__self_0_0) != (*__self_1_0),
                    },
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::Eq for Message {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_total_eq(&self) -> () {
                { let _: ::std::cmp::AssertParamIsEq<Vec<u8>>; }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::clone::Clone for Message {
            #[inline]
            fn clone(&self) -> Message {
                match *self {
                    Message(ref __self_0_0) =>
                    Message(::std::clone::Clone::clone(&(*__self_0_0))),
                }
            }
        }
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_SERIALIZE_FOR_Message: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl _serde::Serialize for Message {
                    fn serialize<__S>(&self, __serializer: __S)
                     -> _serde::export::Result<__S::Ok, __S::Error> where
                     __S: _serde::Serializer {
                        _serde::Serializer::serialize_newtype_struct(__serializer,
                                                                     "Message",
                                                                     {
                                                                         struct __SerializeWith<'__a> {
                                                                             values: (&'__a Vec<u8>,),
                                                                             phantom: _serde::export::PhantomData<Message>,
                                                                         }
                                                                         impl <'__a>
                                                                          _serde::Serialize
                                                                          for
                                                                          __SerializeWith<'__a>
                                                                          {
                                                                             fn serialize<__S>(&self,
                                                                                               __s:
                                                                                                   __S)
                                                                              ->
                                                                                  _serde::export::Result<__S::Ok,
                                                                                                         __S::Error>
                                                                              where
                                                                              __S: _serde::Serializer {
                                                                                 bytes::serialize(self.values.0,
                                                                                                  __s)
                                                                             }
                                                                         }
                                                                         &__SerializeWith{values:
                                                                                              (&self.0,),
                                                                                          phantom:
                                                                                              _serde::export::PhantomData::<Message>,}
                                                                     })
                    }
                }
            };
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_DESERIALIZE_FOR_Message: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl <'de> _serde::Deserialize<'de> for Message {
                    fn deserialize<__D>(__deserializer: __D)
                     -> _serde::export::Result<Self, __D::Error> where
                     __D: _serde::Deserializer<'de> {
                        struct __Visitor<'de> {
                            marker: _serde::export::PhantomData<Message>,
                            lifetime: _serde::export::PhantomData<&'de ()>,
                        }
                        impl <'de> _serde::de::Visitor<'de> for __Visitor<'de>
                         {
                            type
                            Value
                            =
                            Message;
                            fn expecting(&self,
                                         __formatter:
                                             &mut _serde::export::Formatter)
                             -> _serde::export::fmt::Result {
                                _serde::export::Formatter::write_str(__formatter,
                                                                     "tuple struct Message")
                            }
                            #[inline]
                            fn visit_newtype_struct<__E>(self, __e: __E)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __E::Error> where
                             __E: _serde::Deserializer<'de> {
                                let __field0: Vec<u8> =
                                    match bytes::deserialize(__e) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    };
                                _serde::export::Ok(Message(__field0))
                            }
                            #[inline]
                            fn visit_seq<__A>(self, mut __seq: __A)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __A::Error> where
                             __A: _serde::de::SeqAccess<'de> {
                                let __field0 =
                                    match {
                                              struct __DeserializeWith<'de> {
                                                  value: Vec<u8>,
                                                  phantom: _serde::export::PhantomData<Message>,
                                                  lifetime: _serde::export::PhantomData<&'de ()>,
                                              }
                                              impl <'de>
                                               _serde::Deserialize<'de> for
                                               __DeserializeWith<'de> {
                                                  fn deserialize<__D>(__deserializer:
                                                                          __D)
                                                   ->
                                                       _serde::export::Result<Self,
                                                                              __D::Error>
                                                   where
                                                   __D: _serde::Deserializer<'de> {
                                                      _serde::export::Ok(__DeserializeWith{value:
                                                                                               match bytes::deserialize(__deserializer)
                                                                                                   {
                                                                                                   _serde::export::Ok(__val)
                                                                                                   =>
                                                                                                   __val,
                                                                                                   _serde::export::Err(__err)
                                                                                                   =>
                                                                                                   {
                                                                                                       return _serde::export::Err(__err);
                                                                                                   }
                                                                                               },
                                                                                           phantom:
                                                                                               _serde::export::PhantomData,
                                                                                           lifetime:
                                                                                               _serde::export::PhantomData,})
                                                  }
                                              }
                                              _serde::export::Option::map(match _serde::de::SeqAccess::next_element::<__DeserializeWith<'de>>(&mut __seq)
                                                                              {
                                                                              _serde::export::Ok(__val)
                                                                              =>
                                                                              __val,
                                                                              _serde::export::Err(__err)
                                                                              =>
                                                                              {
                                                                                  return _serde::export::Err(__err);
                                                                              }
                                                                          },
                                                                          |__wrap|
                                                                              __wrap.value)
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(0usize,
                                                                                                         &"tuple struct Message with 1 element"));
                                        }
                                    };
                                _serde::export::Ok(Message(__field0))
                            }
                        }
                        _serde::Deserializer::deserialize_newtype_struct(__deserializer,
                                                                         "Message",
                                                                         __Visitor{marker:
                                                                                       _serde::export::PhantomData::<Message>,
                                                                                   lifetime:
                                                                                       _serde::export::PhantomData,})
                    }
                }
            };
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::fmt::Debug for Message {
            fn fmt(&self, f: &mut ::std::fmt::Formatter)
             -> ::std::fmt::Result {
                match *self {
                    Message(ref __self_0_0) => {
                        let mut debug_trait_builder =
                            f.debug_tuple("Message");
                        let _ = debug_trait_builder.field(&&(*__self_0_0));
                        debug_trait_builder.finish()
                    }
                }
            }
        }
        /// Consolidated ingress queue data.
        ///
        /// This is just an ordered vector of other parachains' egress queues,
        /// obtained according to the routing rules.
        #[structural_match]
        pub struct ConsolidatedIngress(pub Vec<(Id, Vec<Message>)>);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::default::Default for ConsolidatedIngress {
            #[inline]
            fn default() -> ConsolidatedIngress {
                ConsolidatedIngress(::std::default::Default::default())
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialEq for ConsolidatedIngress {
            #[inline]
            fn eq(&self, other: &ConsolidatedIngress) -> bool {
                match *other {
                    ConsolidatedIngress(ref __self_1_0) =>
                    match *self {
                        ConsolidatedIngress(ref __self_0_0) =>
                        (*__self_0_0) == (*__self_1_0),
                    },
                }
            }
            #[inline]
            fn ne(&self, other: &ConsolidatedIngress) -> bool {
                match *other {
                    ConsolidatedIngress(ref __self_1_0) =>
                    match *self {
                        ConsolidatedIngress(ref __self_0_0) =>
                        (*__self_0_0) != (*__self_1_0),
                    },
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::Eq for ConsolidatedIngress {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _:
                            ::std::cmp::AssertParamIsEq<Vec<(Id,
                                                             Vec<Message>)>>;
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::clone::Clone for ConsolidatedIngress {
            #[inline]
            fn clone(&self) -> ConsolidatedIngress {
                match *self {
                    ConsolidatedIngress(ref __self_0_0) =>
                    ConsolidatedIngress(::std::clone::Clone::clone(&(*__self_0_0))),
                }
            }
        }
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_SERIALIZE_FOR_ConsolidatedIngress: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl _serde::Serialize for ConsolidatedIngress {
                    fn serialize<__S>(&self, __serializer: __S)
                     -> _serde::export::Result<__S::Ok, __S::Error> where
                     __S: _serde::Serializer {
                        _serde::Serializer::serialize_newtype_struct(__serializer,
                                                                     "ConsolidatedIngress",
                                                                     &self.0)
                    }
                }
            };
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_DESERIALIZE_FOR_ConsolidatedIngress: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl <'de> _serde::Deserialize<'de> for ConsolidatedIngress {
                    fn deserialize<__D>(__deserializer: __D)
                     -> _serde::export::Result<Self, __D::Error> where
                     __D: _serde::Deserializer<'de> {
                        struct __Visitor<'de> {
                            marker: _serde::export::PhantomData<ConsolidatedIngress>,
                            lifetime: _serde::export::PhantomData<&'de ()>,
                        }
                        impl <'de> _serde::de::Visitor<'de> for __Visitor<'de>
                         {
                            type
                            Value
                            =
                            ConsolidatedIngress;
                            fn expecting(&self,
                                         __formatter:
                                             &mut _serde::export::Formatter)
                             -> _serde::export::fmt::Result {
                                _serde::export::Formatter::write_str(__formatter,
                                                                     "tuple struct ConsolidatedIngress")
                            }
                            #[inline]
                            fn visit_newtype_struct<__E>(self, __e: __E)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __E::Error> where
                             __E: _serde::Deserializer<'de> {
                                let __field0: Vec<(Id, Vec<Message>)> =
                                    match <Vec<(Id, Vec<Message>)> as
                                              _serde::Deserialize>::deserialize(__e)
                                        {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    };
                                _serde::export::Ok(ConsolidatedIngress(__field0))
                            }
                            #[inline]
                            fn visit_seq<__A>(self, mut __seq: __A)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __A::Error> where
                             __A: _serde::de::SeqAccess<'de> {
                                let __field0 =
                                    match match _serde::de::SeqAccess::next_element::<Vec<(Id,
                                                                                           Vec<Message>)>>(&mut __seq)
                                              {
                                              _serde::export::Ok(__val) =>
                                              __val,
                                              _serde::export::Err(__err) => {
                                                  return _serde::export::Err(__err);
                                              }
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(0usize,
                                                                                                         &"tuple struct ConsolidatedIngress with 1 element"));
                                        }
                                    };
                                _serde::export::Ok(ConsolidatedIngress(__field0))
                            }
                        }
                        _serde::Deserializer::deserialize_newtype_struct(__deserializer,
                                                                         "ConsolidatedIngress",
                                                                         __Visitor{marker:
                                                                                       _serde::export::PhantomData::<ConsolidatedIngress>,
                                                                                   lifetime:
                                                                                       _serde::export::PhantomData,})
                    }
                }
            };
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::fmt::Debug for ConsolidatedIngress {
            fn fmt(&self, f: &mut ::std::fmt::Formatter)
             -> ::std::fmt::Result {
                match *self {
                    ConsolidatedIngress(ref __self_0_0) => {
                        let mut debug_trait_builder =
                            f.debug_tuple("ConsolidatedIngress");
                        let _ = debug_trait_builder.field(&&(*__self_0_0));
                        debug_trait_builder.finish()
                    }
                }
            }
        }
        /// Parachain block data.
        ///
        /// contains everything required to validate para-block, may contain block and witness data
        #[structural_match]
        pub struct BlockData(
                             #[serde(with = "bytes")]
                             pub Vec<u8>);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialEq for BlockData {
            #[inline]
            fn eq(&self, other: &BlockData) -> bool {
                match *other {
                    BlockData(ref __self_1_0) =>
                    match *self {
                        BlockData(ref __self_0_0) =>
                        (*__self_0_0) == (*__self_1_0),
                    },
                }
            }
            #[inline]
            fn ne(&self, other: &BlockData) -> bool {
                match *other {
                    BlockData(ref __self_1_0) =>
                    match *self {
                        BlockData(ref __self_0_0) =>
                        (*__self_0_0) != (*__self_1_0),
                    },
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::Eq for BlockData {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_total_eq(&self) -> () {
                { let _: ::std::cmp::AssertParamIsEq<Vec<u8>>; }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::clone::Clone for BlockData {
            #[inline]
            fn clone(&self) -> BlockData {
                match *self {
                    BlockData(ref __self_0_0) =>
                    BlockData(::std::clone::Clone::clone(&(*__self_0_0))),
                }
            }
        }
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_SERIALIZE_FOR_BlockData: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl _serde::Serialize for BlockData {
                    fn serialize<__S>(&self, __serializer: __S)
                     -> _serde::export::Result<__S::Ok, __S::Error> where
                     __S: _serde::Serializer {
                        _serde::Serializer::serialize_newtype_struct(__serializer,
                                                                     "BlockData",
                                                                     {
                                                                         struct __SerializeWith<'__a> {
                                                                             values: (&'__a Vec<u8>,),
                                                                             phantom: _serde::export::PhantomData<BlockData>,
                                                                         }
                                                                         impl <'__a>
                                                                          _serde::Serialize
                                                                          for
                                                                          __SerializeWith<'__a>
                                                                          {
                                                                             fn serialize<__S>(&self,
                                                                                               __s:
                                                                                                   __S)
                                                                              ->
                                                                                  _serde::export::Result<__S::Ok,
                                                                                                         __S::Error>
                                                                              where
                                                                              __S: _serde::Serializer {
                                                                                 bytes::serialize(self.values.0,
                                                                                                  __s)
                                                                             }
                                                                         }
                                                                         &__SerializeWith{values:
                                                                                              (&self.0,),
                                                                                          phantom:
                                                                                              _serde::export::PhantomData::<BlockData>,}
                                                                     })
                    }
                }
            };
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_DESERIALIZE_FOR_BlockData: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl <'de> _serde::Deserialize<'de> for BlockData {
                    fn deserialize<__D>(__deserializer: __D)
                     -> _serde::export::Result<Self, __D::Error> where
                     __D: _serde::Deserializer<'de> {
                        struct __Visitor<'de> {
                            marker: _serde::export::PhantomData<BlockData>,
                            lifetime: _serde::export::PhantomData<&'de ()>,
                        }
                        impl <'de> _serde::de::Visitor<'de> for __Visitor<'de>
                         {
                            type
                            Value
                            =
                            BlockData;
                            fn expecting(&self,
                                         __formatter:
                                             &mut _serde::export::Formatter)
                             -> _serde::export::fmt::Result {
                                _serde::export::Formatter::write_str(__formatter,
                                                                     "tuple struct BlockData")
                            }
                            #[inline]
                            fn visit_newtype_struct<__E>(self, __e: __E)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __E::Error> where
                             __E: _serde::Deserializer<'de> {
                                let __field0: Vec<u8> =
                                    match bytes::deserialize(__e) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    };
                                _serde::export::Ok(BlockData(__field0))
                            }
                            #[inline]
                            fn visit_seq<__A>(self, mut __seq: __A)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __A::Error> where
                             __A: _serde::de::SeqAccess<'de> {
                                let __field0 =
                                    match {
                                              struct __DeserializeWith<'de> {
                                                  value: Vec<u8>,
                                                  phantom: _serde::export::PhantomData<BlockData>,
                                                  lifetime: _serde::export::PhantomData<&'de ()>,
                                              }
                                              impl <'de>
                                               _serde::Deserialize<'de> for
                                               __DeserializeWith<'de> {
                                                  fn deserialize<__D>(__deserializer:
                                                                          __D)
                                                   ->
                                                       _serde::export::Result<Self,
                                                                              __D::Error>
                                                   where
                                                   __D: _serde::Deserializer<'de> {
                                                      _serde::export::Ok(__DeserializeWith{value:
                                                                                               match bytes::deserialize(__deserializer)
                                                                                                   {
                                                                                                   _serde::export::Ok(__val)
                                                                                                   =>
                                                                                                   __val,
                                                                                                   _serde::export::Err(__err)
                                                                                                   =>
                                                                                                   {
                                                                                                       return _serde::export::Err(__err);
                                                                                                   }
                                                                                               },
                                                                                           phantom:
                                                                                               _serde::export::PhantomData,
                                                                                           lifetime:
                                                                                               _serde::export::PhantomData,})
                                                  }
                                              }
                                              _serde::export::Option::map(match _serde::de::SeqAccess::next_element::<__DeserializeWith<'de>>(&mut __seq)
                                                                              {
                                                                              _serde::export::Ok(__val)
                                                                              =>
                                                                              __val,
                                                                              _serde::export::Err(__err)
                                                                              =>
                                                                              {
                                                                                  return _serde::export::Err(__err);
                                                                              }
                                                                          },
                                                                          |__wrap|
                                                                              __wrap.value)
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(0usize,
                                                                                                         &"tuple struct BlockData with 1 element"));
                                        }
                                    };
                                _serde::export::Ok(BlockData(__field0))
                            }
                        }
                        _serde::Deserializer::deserialize_newtype_struct(__deserializer,
                                                                         "BlockData",
                                                                         __Visitor{marker:
                                                                                       _serde::export::PhantomData::<BlockData>,
                                                                                   lifetime:
                                                                                       _serde::export::PhantomData,})
                    }
                }
            };
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::fmt::Debug for BlockData {
            fn fmt(&self, f: &mut ::std::fmt::Formatter)
             -> ::std::fmt::Result {
                match *self {
                    BlockData(ref __self_0_0) => {
                        let mut debug_trait_builder =
                            f.debug_tuple("BlockData");
                        let _ = debug_trait_builder.field(&&(*__self_0_0));
                        debug_trait_builder.finish()
                    }
                }
            }
        }
        /// Parachain header raw bytes wrapper type.
        #[structural_match]
        pub struct Header(
                          #[serde(with = "bytes")]
                          pub Vec<u8>);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialEq for Header {
            #[inline]
            fn eq(&self, other: &Header) -> bool {
                match *other {
                    Header(ref __self_1_0) =>
                    match *self {
                        Header(ref __self_0_0) =>
                        (*__self_0_0) == (*__self_1_0),
                    },
                }
            }
            #[inline]
            fn ne(&self, other: &Header) -> bool {
                match *other {
                    Header(ref __self_1_0) =>
                    match *self {
                        Header(ref __self_0_0) =>
                        (*__self_0_0) != (*__self_1_0),
                    },
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::Eq for Header {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_total_eq(&self) -> () {
                { let _: ::std::cmp::AssertParamIsEq<Vec<u8>>; }
            }
        }
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_SERIALIZE_FOR_Header: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl _serde::Serialize for Header {
                    fn serialize<__S>(&self, __serializer: __S)
                     -> _serde::export::Result<__S::Ok, __S::Error> where
                     __S: _serde::Serializer {
                        _serde::Serializer::serialize_newtype_struct(__serializer,
                                                                     "Header",
                                                                     {
                                                                         struct __SerializeWith<'__a> {
                                                                             values: (&'__a Vec<u8>,),
                                                                             phantom: _serde::export::PhantomData<Header>,
                                                                         }
                                                                         impl <'__a>
                                                                          _serde::Serialize
                                                                          for
                                                                          __SerializeWith<'__a>
                                                                          {
                                                                             fn serialize<__S>(&self,
                                                                                               __s:
                                                                                                   __S)
                                                                              ->
                                                                                  _serde::export::Result<__S::Ok,
                                                                                                         __S::Error>
                                                                              where
                                                                              __S: _serde::Serializer {
                                                                                 bytes::serialize(self.values.0,
                                                                                                  __s)
                                                                             }
                                                                         }
                                                                         &__SerializeWith{values:
                                                                                              (&self.0,),
                                                                                          phantom:
                                                                                              _serde::export::PhantomData::<Header>,}
                                                                     })
                    }
                }
            };
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_DESERIALIZE_FOR_Header: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl <'de> _serde::Deserialize<'de> for Header {
                    fn deserialize<__D>(__deserializer: __D)
                     -> _serde::export::Result<Self, __D::Error> where
                     __D: _serde::Deserializer<'de> {
                        struct __Visitor<'de> {
                            marker: _serde::export::PhantomData<Header>,
                            lifetime: _serde::export::PhantomData<&'de ()>,
                        }
                        impl <'de> _serde::de::Visitor<'de> for __Visitor<'de>
                         {
                            type
                            Value
                            =
                            Header;
                            fn expecting(&self,
                                         __formatter:
                                             &mut _serde::export::Formatter)
                             -> _serde::export::fmt::Result {
                                _serde::export::Formatter::write_str(__formatter,
                                                                     "tuple struct Header")
                            }
                            #[inline]
                            fn visit_newtype_struct<__E>(self, __e: __E)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __E::Error> where
                             __E: _serde::Deserializer<'de> {
                                let __field0: Vec<u8> =
                                    match bytes::deserialize(__e) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    };
                                _serde::export::Ok(Header(__field0))
                            }
                            #[inline]
                            fn visit_seq<__A>(self, mut __seq: __A)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __A::Error> where
                             __A: _serde::de::SeqAccess<'de> {
                                let __field0 =
                                    match {
                                              struct __DeserializeWith<'de> {
                                                  value: Vec<u8>,
                                                  phantom: _serde::export::PhantomData<Header>,
                                                  lifetime: _serde::export::PhantomData<&'de ()>,
                                              }
                                              impl <'de>
                                               _serde::Deserialize<'de> for
                                               __DeserializeWith<'de> {
                                                  fn deserialize<__D>(__deserializer:
                                                                          __D)
                                                   ->
                                                       _serde::export::Result<Self,
                                                                              __D::Error>
                                                   where
                                                   __D: _serde::Deserializer<'de> {
                                                      _serde::export::Ok(__DeserializeWith{value:
                                                                                               match bytes::deserialize(__deserializer)
                                                                                                   {
                                                                                                   _serde::export::Ok(__val)
                                                                                                   =>
                                                                                                   __val,
                                                                                                   _serde::export::Err(__err)
                                                                                                   =>
                                                                                                   {
                                                                                                       return _serde::export::Err(__err);
                                                                                                   }
                                                                                               },
                                                                                           phantom:
                                                                                               _serde::export::PhantomData,
                                                                                           lifetime:
                                                                                               _serde::export::PhantomData,})
                                                  }
                                              }
                                              _serde::export::Option::map(match _serde::de::SeqAccess::next_element::<__DeserializeWith<'de>>(&mut __seq)
                                                                              {
                                                                              _serde::export::Ok(__val)
                                                                              =>
                                                                              __val,
                                                                              _serde::export::Err(__err)
                                                                              =>
                                                                              {
                                                                                  return _serde::export::Err(__err);
                                                                              }
                                                                          },
                                                                          |__wrap|
                                                                              __wrap.value)
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(0usize,
                                                                                                         &"tuple struct Header with 1 element"));
                                        }
                                    };
                                _serde::export::Ok(Header(__field0))
                            }
                        }
                        _serde::Deserializer::deserialize_newtype_struct(__deserializer,
                                                                         "Header",
                                                                         __Visitor{marker:
                                                                                       _serde::export::PhantomData::<Header>,
                                                                                   lifetime:
                                                                                       _serde::export::PhantomData,})
                    }
                }
            };
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::fmt::Debug for Header {
            fn fmt(&self, f: &mut ::std::fmt::Formatter)
             -> ::std::fmt::Result {
                match *self {
                    Header(ref __self_0_0) => {
                        let mut debug_trait_builder = f.debug_tuple("Header");
                        let _ = debug_trait_builder.field(&&(*__self_0_0));
                        debug_trait_builder.finish()
                    }
                }
            }
        }
        /// Parachain head data included in the chain.
        #[structural_match]
        pub struct HeadData(
                            #[serde(with = "bytes")]
                            pub Vec<u8>);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialEq for HeadData {
            #[inline]
            fn eq(&self, other: &HeadData) -> bool {
                match *other {
                    HeadData(ref __self_1_0) =>
                    match *self {
                        HeadData(ref __self_0_0) =>
                        (*__self_0_0) == (*__self_1_0),
                    },
                }
            }
            #[inline]
            fn ne(&self, other: &HeadData) -> bool {
                match *other {
                    HeadData(ref __self_1_0) =>
                    match *self {
                        HeadData(ref __self_0_0) =>
                        (*__self_0_0) != (*__self_1_0),
                    },
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::Eq for HeadData {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_total_eq(&self) -> () {
                { let _: ::std::cmp::AssertParamIsEq<Vec<u8>>; }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::clone::Clone for HeadData {
            #[inline]
            fn clone(&self) -> HeadData {
                match *self {
                    HeadData(ref __self_0_0) =>
                    HeadData(::std::clone::Clone::clone(&(*__self_0_0))),
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialOrd for HeadData {
            #[inline]
            fn partial_cmp(&self, other: &HeadData)
             -> ::std::option::Option<::std::cmp::Ordering> {
                match *other {
                    HeadData(ref __self_1_0) =>
                    match *self {
                        HeadData(ref __self_0_0) =>
                        match ::std::cmp::PartialOrd::partial_cmp(&(*__self_0_0),
                                                                  &(*__self_1_0))
                            {
                            ::std::option::Option::Some(::std::cmp::Ordering::Equal)
                            =>
                            ::std::option::Option::Some(::std::cmp::Ordering::Equal),
                            cmp => cmp,
                        },
                    },
                }
            }
            #[inline]
            fn lt(&self, other: &HeadData) -> bool {
                match *other {
                    HeadData(ref __self_1_0) =>
                    match *self {
                        HeadData(ref __self_0_0) =>
                        (*__self_0_0) < (*__self_1_0),
                    },
                }
            }
            #[inline]
            fn le(&self, other: &HeadData) -> bool {
                match *other {
                    HeadData(ref __self_1_0) =>
                    match *self {
                        HeadData(ref __self_0_0) =>
                        (*__self_0_0) <= (*__self_1_0),
                    },
                }
            }
            #[inline]
            fn gt(&self, other: &HeadData) -> bool {
                match *other {
                    HeadData(ref __self_1_0) =>
                    match *self {
                        HeadData(ref __self_0_0) =>
                        (*__self_0_0) > (*__self_1_0),
                    },
                }
            }
            #[inline]
            fn ge(&self, other: &HeadData) -> bool {
                match *other {
                    HeadData(ref __self_1_0) =>
                    match *self {
                        HeadData(ref __self_0_0) =>
                        (*__self_0_0) >= (*__self_1_0),
                    },
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::Ord for HeadData {
            #[inline]
            fn cmp(&self, other: &HeadData) -> ::std::cmp::Ordering {
                match *other {
                    HeadData(ref __self_1_0) =>
                    match *self {
                        HeadData(ref __self_0_0) =>
                        match ::std::cmp::Ord::cmp(&(*__self_0_0),
                                                   &(*__self_1_0)) {
                            ::std::cmp::Ordering::Equal =>
                            ::std::cmp::Ordering::Equal,
                            cmp => cmp,
                        },
                    },
                }
            }
        }
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_SERIALIZE_FOR_HeadData: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl _serde::Serialize for HeadData {
                    fn serialize<__S>(&self, __serializer: __S)
                     -> _serde::export::Result<__S::Ok, __S::Error> where
                     __S: _serde::Serializer {
                        _serde::Serializer::serialize_newtype_struct(__serializer,
                                                                     "HeadData",
                                                                     {
                                                                         struct __SerializeWith<'__a> {
                                                                             values: (&'__a Vec<u8>,),
                                                                             phantom: _serde::export::PhantomData<HeadData>,
                                                                         }
                                                                         impl <'__a>
                                                                          _serde::Serialize
                                                                          for
                                                                          __SerializeWith<'__a>
                                                                          {
                                                                             fn serialize<__S>(&self,
                                                                                               __s:
                                                                                                   __S)
                                                                              ->
                                                                                  _serde::export::Result<__S::Ok,
                                                                                                         __S::Error>
                                                                              where
                                                                              __S: _serde::Serializer {
                                                                                 bytes::serialize(self.values.0,
                                                                                                  __s)
                                                                             }
                                                                         }
                                                                         &__SerializeWith{values:
                                                                                              (&self.0,),
                                                                                          phantom:
                                                                                              _serde::export::PhantomData::<HeadData>,}
                                                                     })
                    }
                }
            };
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_DESERIALIZE_FOR_HeadData: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl <'de> _serde::Deserialize<'de> for HeadData {
                    fn deserialize<__D>(__deserializer: __D)
                     -> _serde::export::Result<Self, __D::Error> where
                     __D: _serde::Deserializer<'de> {
                        struct __Visitor<'de> {
                            marker: _serde::export::PhantomData<HeadData>,
                            lifetime: _serde::export::PhantomData<&'de ()>,
                        }
                        impl <'de> _serde::de::Visitor<'de> for __Visitor<'de>
                         {
                            type
                            Value
                            =
                            HeadData;
                            fn expecting(&self,
                                         __formatter:
                                             &mut _serde::export::Formatter)
                             -> _serde::export::fmt::Result {
                                _serde::export::Formatter::write_str(__formatter,
                                                                     "tuple struct HeadData")
                            }
                            #[inline]
                            fn visit_newtype_struct<__E>(self, __e: __E)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __E::Error> where
                             __E: _serde::Deserializer<'de> {
                                let __field0: Vec<u8> =
                                    match bytes::deserialize(__e) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    };
                                _serde::export::Ok(HeadData(__field0))
                            }
                            #[inline]
                            fn visit_seq<__A>(self, mut __seq: __A)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __A::Error> where
                             __A: _serde::de::SeqAccess<'de> {
                                let __field0 =
                                    match {
                                              struct __DeserializeWith<'de> {
                                                  value: Vec<u8>,
                                                  phantom: _serde::export::PhantomData<HeadData>,
                                                  lifetime: _serde::export::PhantomData<&'de ()>,
                                              }
                                              impl <'de>
                                               _serde::Deserialize<'de> for
                                               __DeserializeWith<'de> {
                                                  fn deserialize<__D>(__deserializer:
                                                                          __D)
                                                   ->
                                                       _serde::export::Result<Self,
                                                                              __D::Error>
                                                   where
                                                   __D: _serde::Deserializer<'de> {
                                                      _serde::export::Ok(__DeserializeWith{value:
                                                                                               match bytes::deserialize(__deserializer)
                                                                                                   {
                                                                                                   _serde::export::Ok(__val)
                                                                                                   =>
                                                                                                   __val,
                                                                                                   _serde::export::Err(__err)
                                                                                                   =>
                                                                                                   {
                                                                                                       return _serde::export::Err(__err);
                                                                                                   }
                                                                                               },
                                                                                           phantom:
                                                                                               _serde::export::PhantomData,
                                                                                           lifetime:
                                                                                               _serde::export::PhantomData,})
                                                  }
                                              }
                                              _serde::export::Option::map(match _serde::de::SeqAccess::next_element::<__DeserializeWith<'de>>(&mut __seq)
                                                                              {
                                                                              _serde::export::Ok(__val)
                                                                              =>
                                                                              __val,
                                                                              _serde::export::Err(__err)
                                                                              =>
                                                                              {
                                                                                  return _serde::export::Err(__err);
                                                                              }
                                                                          },
                                                                          |__wrap|
                                                                              __wrap.value)
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(0usize,
                                                                                                         &"tuple struct HeadData with 1 element"));
                                        }
                                    };
                                _serde::export::Ok(HeadData(__field0))
                            }
                        }
                        _serde::Deserializer::deserialize_newtype_struct(__deserializer,
                                                                         "HeadData",
                                                                         __Visitor{marker:
                                                                                       _serde::export::PhantomData::<HeadData>,
                                                                                   lifetime:
                                                                                       _serde::export::PhantomData,})
                    }
                }
            };
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::fmt::Debug for HeadData {
            fn fmt(&self, f: &mut ::std::fmt::Formatter)
             -> ::std::fmt::Result {
                match *self {
                    HeadData(ref __self_0_0) => {
                        let mut debug_trait_builder =
                            f.debug_tuple("HeadData");
                        let _ = debug_trait_builder.field(&&(*__self_0_0));
                        debug_trait_builder.finish()
                    }
                }
            }
        }
        /// Parachain validation code.
        #[structural_match]
        pub struct ValidationCode(
                                  #[serde(with = "bytes")]
                                  pub Vec<u8>);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialEq for ValidationCode {
            #[inline]
            fn eq(&self, other: &ValidationCode) -> bool {
                match *other {
                    ValidationCode(ref __self_1_0) =>
                    match *self {
                        ValidationCode(ref __self_0_0) =>
                        (*__self_0_0) == (*__self_1_0),
                    },
                }
            }
            #[inline]
            fn ne(&self, other: &ValidationCode) -> bool {
                match *other {
                    ValidationCode(ref __self_1_0) =>
                    match *self {
                        ValidationCode(ref __self_0_0) =>
                        (*__self_0_0) != (*__self_1_0),
                    },
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::Eq for ValidationCode {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_total_eq(&self) -> () {
                { let _: ::std::cmp::AssertParamIsEq<Vec<u8>>; }
            }
        }
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_SERIALIZE_FOR_ValidationCode: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl _serde::Serialize for ValidationCode {
                    fn serialize<__S>(&self, __serializer: __S)
                     -> _serde::export::Result<__S::Ok, __S::Error> where
                     __S: _serde::Serializer {
                        _serde::Serializer::serialize_newtype_struct(__serializer,
                                                                     "ValidationCode",
                                                                     {
                                                                         struct __SerializeWith<'__a> {
                                                                             values: (&'__a Vec<u8>,),
                                                                             phantom: _serde::export::PhantomData<ValidationCode>,
                                                                         }
                                                                         impl <'__a>
                                                                          _serde::Serialize
                                                                          for
                                                                          __SerializeWith<'__a>
                                                                          {
                                                                             fn serialize<__S>(&self,
                                                                                               __s:
                                                                                                   __S)
                                                                              ->
                                                                                  _serde::export::Result<__S::Ok,
                                                                                                         __S::Error>
                                                                              where
                                                                              __S: _serde::Serializer {
                                                                                 bytes::serialize(self.values.0,
                                                                                                  __s)
                                                                             }
                                                                         }
                                                                         &__SerializeWith{values:
                                                                                              (&self.0,),
                                                                                          phantom:
                                                                                              _serde::export::PhantomData::<ValidationCode>,}
                                                                     })
                    }
                }
            };
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_DESERIALIZE_FOR_ValidationCode: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl <'de> _serde::Deserialize<'de> for ValidationCode {
                    fn deserialize<__D>(__deserializer: __D)
                     -> _serde::export::Result<Self, __D::Error> where
                     __D: _serde::Deserializer<'de> {
                        struct __Visitor<'de> {
                            marker: _serde::export::PhantomData<ValidationCode>,
                            lifetime: _serde::export::PhantomData<&'de ()>,
                        }
                        impl <'de> _serde::de::Visitor<'de> for __Visitor<'de>
                         {
                            type
                            Value
                            =
                            ValidationCode;
                            fn expecting(&self,
                                         __formatter:
                                             &mut _serde::export::Formatter)
                             -> _serde::export::fmt::Result {
                                _serde::export::Formatter::write_str(__formatter,
                                                                     "tuple struct ValidationCode")
                            }
                            #[inline]
                            fn visit_newtype_struct<__E>(self, __e: __E)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __E::Error> where
                             __E: _serde::Deserializer<'de> {
                                let __field0: Vec<u8> =
                                    match bytes::deserialize(__e) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    };
                                _serde::export::Ok(ValidationCode(__field0))
                            }
                            #[inline]
                            fn visit_seq<__A>(self, mut __seq: __A)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __A::Error> where
                             __A: _serde::de::SeqAccess<'de> {
                                let __field0 =
                                    match {
                                              struct __DeserializeWith<'de> {
                                                  value: Vec<u8>,
                                                  phantom: _serde::export::PhantomData<ValidationCode>,
                                                  lifetime: _serde::export::PhantomData<&'de ()>,
                                              }
                                              impl <'de>
                                               _serde::Deserialize<'de> for
                                               __DeserializeWith<'de> {
                                                  fn deserialize<__D>(__deserializer:
                                                                          __D)
                                                   ->
                                                       _serde::export::Result<Self,
                                                                              __D::Error>
                                                   where
                                                   __D: _serde::Deserializer<'de> {
                                                      _serde::export::Ok(__DeserializeWith{value:
                                                                                               match bytes::deserialize(__deserializer)
                                                                                                   {
                                                                                                   _serde::export::Ok(__val)
                                                                                                   =>
                                                                                                   __val,
                                                                                                   _serde::export::Err(__err)
                                                                                                   =>
                                                                                                   {
                                                                                                       return _serde::export::Err(__err);
                                                                                                   }
                                                                                               },
                                                                                           phantom:
                                                                                               _serde::export::PhantomData,
                                                                                           lifetime:
                                                                                               _serde::export::PhantomData,})
                                                  }
                                              }
                                              _serde::export::Option::map(match _serde::de::SeqAccess::next_element::<__DeserializeWith<'de>>(&mut __seq)
                                                                              {
                                                                              _serde::export::Ok(__val)
                                                                              =>
                                                                              __val,
                                                                              _serde::export::Err(__err)
                                                                              =>
                                                                              {
                                                                                  return _serde::export::Err(__err);
                                                                              }
                                                                          },
                                                                          |__wrap|
                                                                              __wrap.value)
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(0usize,
                                                                                                         &"tuple struct ValidationCode with 1 element"));
                                        }
                                    };
                                _serde::export::Ok(ValidationCode(__field0))
                            }
                        }
                        _serde::Deserializer::deserialize_newtype_struct(__deserializer,
                                                                         "ValidationCode",
                                                                         __Visitor{marker:
                                                                                       _serde::export::PhantomData::<ValidationCode>,
                                                                                   lifetime:
                                                                                       _serde::export::PhantomData,})
                    }
                }
            };
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::fmt::Debug for ValidationCode {
            fn fmt(&self, f: &mut ::std::fmt::Formatter)
             -> ::std::fmt::Result {
                match *self {
                    ValidationCode(ref __self_0_0) => {
                        let mut debug_trait_builder =
                            f.debug_tuple("ValidationCode");
                        let _ = debug_trait_builder.field(&&(*__self_0_0));
                        debug_trait_builder.finish()
                    }
                }
            }
        }
        /// Activitiy bit field
        #[structural_match]
        pub struct Activity(
                            #[serde(with = "bytes")]
                            pub Vec<u8>);
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialEq for Activity {
            #[inline]
            fn eq(&self, other: &Activity) -> bool {
                match *other {
                    Activity(ref __self_1_0) =>
                    match *self {
                        Activity(ref __self_0_0) =>
                        (*__self_0_0) == (*__self_1_0),
                    },
                }
            }
            #[inline]
            fn ne(&self, other: &Activity) -> bool {
                match *other {
                    Activity(ref __self_1_0) =>
                    match *self {
                        Activity(ref __self_0_0) =>
                        (*__self_0_0) != (*__self_1_0),
                    },
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::Eq for Activity {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_total_eq(&self) -> () {
                { let _: ::std::cmp::AssertParamIsEq<Vec<u8>>; }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::clone::Clone for Activity {
            #[inline]
            fn clone(&self) -> Activity {
                match *self {
                    Activity(ref __self_0_0) =>
                    Activity(::std::clone::Clone::clone(&(*__self_0_0))),
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::default::Default for Activity {
            #[inline]
            fn default() -> Activity {
                Activity(::std::default::Default::default())
            }
        }
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_SERIALIZE_FOR_Activity: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl _serde::Serialize for Activity {
                    fn serialize<__S>(&self, __serializer: __S)
                     -> _serde::export::Result<__S::Ok, __S::Error> where
                     __S: _serde::Serializer {
                        _serde::Serializer::serialize_newtype_struct(__serializer,
                                                                     "Activity",
                                                                     {
                                                                         struct __SerializeWith<'__a> {
                                                                             values: (&'__a Vec<u8>,),
                                                                             phantom: _serde::export::PhantomData<Activity>,
                                                                         }
                                                                         impl <'__a>
                                                                          _serde::Serialize
                                                                          for
                                                                          __SerializeWith<'__a>
                                                                          {
                                                                             fn serialize<__S>(&self,
                                                                                               __s:
                                                                                                   __S)
                                                                              ->
                                                                                  _serde::export::Result<__S::Ok,
                                                                                                         __S::Error>
                                                                              where
                                                                              __S: _serde::Serializer {
                                                                                 bytes::serialize(self.values.0,
                                                                                                  __s)
                                                                             }
                                                                         }
                                                                         &__SerializeWith{values:
                                                                                              (&self.0,),
                                                                                          phantom:
                                                                                              _serde::export::PhantomData::<Activity>,}
                                                                     })
                    }
                }
            };
        #[allow(non_upper_case_globals,
                unused_attributes,
                unused_qualifications)]
        const _IMPL_DESERIALIZE_FOR_Activity: () =
            {
                extern crate serde as _serde;
                #[allow(unused_macros)]
                macro_rules! try(( $ __expr : expr ) => {
                                 match $ __expr {
                                 _serde :: export :: Ok ( __val ) => __val ,
                                 _serde :: export :: Err ( __err ) => {
                                 return _serde :: export :: Err ( __err ) ; }
                                 } });
                #[automatically_derived]
                impl <'de> _serde::Deserialize<'de> for Activity {
                    fn deserialize<__D>(__deserializer: __D)
                     -> _serde::export::Result<Self, __D::Error> where
                     __D: _serde::Deserializer<'de> {
                        struct __Visitor<'de> {
                            marker: _serde::export::PhantomData<Activity>,
                            lifetime: _serde::export::PhantomData<&'de ()>,
                        }
                        impl <'de> _serde::de::Visitor<'de> for __Visitor<'de>
                         {
                            type
                            Value
                            =
                            Activity;
                            fn expecting(&self,
                                         __formatter:
                                             &mut _serde::export::Formatter)
                             -> _serde::export::fmt::Result {
                                _serde::export::Formatter::write_str(__formatter,
                                                                     "tuple struct Activity")
                            }
                            #[inline]
                            fn visit_newtype_struct<__E>(self, __e: __E)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __E::Error> where
                             __E: _serde::Deserializer<'de> {
                                let __field0: Vec<u8> =
                                    match bytes::deserialize(__e) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    };
                                _serde::export::Ok(Activity(__field0))
                            }
                            #[inline]
                            fn visit_seq<__A>(self, mut __seq: __A)
                             ->
                                 _serde::export::Result<Self::Value,
                                                        __A::Error> where
                             __A: _serde::de::SeqAccess<'de> {
                                let __field0 =
                                    match {
                                              struct __DeserializeWith<'de> {
                                                  value: Vec<u8>,
                                                  phantom: _serde::export::PhantomData<Activity>,
                                                  lifetime: _serde::export::PhantomData<&'de ()>,
                                              }
                                              impl <'de>
                                               _serde::Deserialize<'de> for
                                               __DeserializeWith<'de> {
                                                  fn deserialize<__D>(__deserializer:
                                                                          __D)
                                                   ->
                                                       _serde::export::Result<Self,
                                                                              __D::Error>
                                                   where
                                                   __D: _serde::Deserializer<'de> {
                                                      _serde::export::Ok(__DeserializeWith{value:
                                                                                               match bytes::deserialize(__deserializer)
                                                                                                   {
                                                                                                   _serde::export::Ok(__val)
                                                                                                   =>
                                                                                                   __val,
                                                                                                   _serde::export::Err(__err)
                                                                                                   =>
                                                                                                   {
                                                                                                       return _serde::export::Err(__err);
                                                                                                   }
                                                                                               },
                                                                                           phantom:
                                                                                               _serde::export::PhantomData,
                                                                                           lifetime:
                                                                                               _serde::export::PhantomData,})
                                                  }
                                              }
                                              _serde::export::Option::map(match _serde::de::SeqAccess::next_element::<__DeserializeWith<'de>>(&mut __seq)
                                                                              {
                                                                              _serde::export::Ok(__val)
                                                                              =>
                                                                              __val,
                                                                              _serde::export::Err(__err)
                                                                              =>
                                                                              {
                                                                                  return _serde::export::Err(__err);
                                                                              }
                                                                          },
                                                                          |__wrap|
                                                                              __wrap.value)
                                          } {
                                        _serde::export::Some(__value) =>
                                        __value,
                                        _serde::export::None => {
                                            return _serde::export::Err(_serde::de::Error::invalid_length(0usize,
                                                                                                         &"tuple struct Activity with 1 element"));
                                        }
                                    };
                                _serde::export::Ok(Activity(__field0))
                            }
                        }
                        _serde::Deserializer::deserialize_newtype_struct(__deserializer,
                                                                         "Activity",
                                                                         __Visitor{marker:
                                                                                       _serde::export::PhantomData::<Activity>,
                                                                                   lifetime:
                                                                                       _serde::export::PhantomData,})
                    }
                }
            };
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::fmt::Debug for Activity {
            fn fmt(&self, f: &mut ::std::fmt::Formatter)
             -> ::std::fmt::Result {
                match *self {
                    Activity(ref __self_0_0) => {
                        let mut debug_trait_builder =
                            f.debug_tuple("Activity");
                        let _ = debug_trait_builder.field(&&(*__self_0_0));
                        debug_trait_builder.finish()
                    }
                }
            }
        }
        impl Slicable for Activity {
            fn decode<I: Input>(input: &mut I) -> Option<Self> {
                Vec::<u8>::decode(input).map(Activity)
            }
            fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
                self.0.using_encoded(f)
            }
        }
        #[repr(u8)]
        #[structural_match]
        #[rustc_copy_clone_marker]
        enum StatementKind {
            Candidate = 1,
            Valid = 2,
            Invalid = 3,
            Available = 4,
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::clone::Clone for StatementKind {
            #[inline]
            fn clone(&self) -> StatementKind { { *self } }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::marker::Copy for StatementKind { }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialEq for StatementKind {
            #[inline]
            fn eq(&self, other: &StatementKind) -> bool {
                {
                    let __self_vi =
                        unsafe {
                            ::std::intrinsics::discriminant_value(&*self)
                        } as u8;
                    let __arg_1_vi =
                        unsafe {
                            ::std::intrinsics::discriminant_value(&*other)
                        } as u8;
                    if true && __self_vi == __arg_1_vi {
                        match (&*self, &*other) { _ => true, }
                    } else { false }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::Eq for StatementKind {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_total_eq(&self) -> () { { } }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::fmt::Debug for StatementKind {
            fn fmt(&self, f: &mut ::std::fmt::Formatter)
             -> ::std::fmt::Result {
                match (&*self,) {
                    (&StatementKind::Candidate,) => {
                        let mut debug_trait_builder =
                            f.debug_tuple("Candidate");
                        debug_trait_builder.finish()
                    }
                    (&StatementKind::Valid,) => {
                        let mut debug_trait_builder = f.debug_tuple("Valid");
                        debug_trait_builder.finish()
                    }
                    (&StatementKind::Invalid,) => {
                        let mut debug_trait_builder =
                            f.debug_tuple("Invalid");
                        debug_trait_builder.finish()
                    }
                    (&StatementKind::Available,) => {
                        let mut debug_trait_builder =
                            f.debug_tuple("Available");
                        debug_trait_builder.finish()
                    }
                }
            }
        }
        /// Statements which can be made about parachain candidates.
        #[structural_match]
        pub enum Statement {

            /// Proposal of a parachain candidate.
            Candidate(CandidateReceipt),

            /// State that a parachain candidate is valid.
            Valid(Hash),

            /// Vote to commit to a candidate.
            Invalid(Hash),

            /// Vote to advance round after inactive primary.
            Available(Hash),
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::clone::Clone for Statement {
            #[inline]
            fn clone(&self) -> Statement {
                match (&*self,) {
                    (&Statement::Candidate(ref __self_0),) =>
                    Statement::Candidate(::std::clone::Clone::clone(&(*__self_0))),
                    (&Statement::Valid(ref __self_0),) =>
                    Statement::Valid(::std::clone::Clone::clone(&(*__self_0))),
                    (&Statement::Invalid(ref __self_0),) =>
                    Statement::Invalid(::std::clone::Clone::clone(&(*__self_0))),
                    (&Statement::Available(ref __self_0),) =>
                    Statement::Available(::std::clone::Clone::clone(&(*__self_0))),
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::PartialEq for Statement {
            #[inline]
            fn eq(&self, other: &Statement) -> bool {
                {
                    let __self_vi =
                        unsafe {
                            ::std::intrinsics::discriminant_value(&*self)
                        } as isize;
                    let __arg_1_vi =
                        unsafe {
                            ::std::intrinsics::discriminant_value(&*other)
                        } as isize;
                    if true && __self_vi == __arg_1_vi {
                        match (&*self, &*other) {
                            (&Statement::Candidate(ref __self_0),
                             &Statement::Candidate(ref __arg_1_0)) =>
                            (*__self_0) == (*__arg_1_0),
                            (&Statement::Valid(ref __self_0),
                             &Statement::Valid(ref __arg_1_0)) =>
                            (*__self_0) == (*__arg_1_0),
                            (&Statement::Invalid(ref __self_0),
                             &Statement::Invalid(ref __arg_1_0)) =>
                            (*__self_0) == (*__arg_1_0),
                            (&Statement::Available(ref __self_0),
                             &Statement::Available(ref __arg_1_0)) =>
                            (*__self_0) == (*__arg_1_0),
                            _ => unsafe { ::std::intrinsics::unreachable() }
                        }
                    } else { false }
                }
            }
            #[inline]
            fn ne(&self, other: &Statement) -> bool {
                {
                    let __self_vi =
                        unsafe {
                            ::std::intrinsics::discriminant_value(&*self)
                        } as isize;
                    let __arg_1_vi =
                        unsafe {
                            ::std::intrinsics::discriminant_value(&*other)
                        } as isize;
                    if true && __self_vi == __arg_1_vi {
                        match (&*self, &*other) {
                            (&Statement::Candidate(ref __self_0),
                             &Statement::Candidate(ref __arg_1_0)) =>
                            (*__self_0) != (*__arg_1_0),
                            (&Statement::Valid(ref __self_0),
                             &Statement::Valid(ref __arg_1_0)) =>
                            (*__self_0) != (*__arg_1_0),
                            (&Statement::Invalid(ref __self_0),
                             &Statement::Invalid(ref __arg_1_0)) =>
                            (*__self_0) != (*__arg_1_0),
                            (&Statement::Available(ref __self_0),
                             &Statement::Available(ref __arg_1_0)) =>
                            (*__self_0) != (*__arg_1_0),
                            _ => unsafe { ::std::intrinsics::unreachable() }
                        }
                    } else { true }
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::cmp::Eq for Statement {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_total_eq(&self) -> () {
                {
                    let _: ::std::cmp::AssertParamIsEq<CandidateReceipt>;
                    let _: ::std::cmp::AssertParamIsEq<Hash>;
                    let _: ::std::cmp::AssertParamIsEq<Hash>;
                    let _: ::std::cmp::AssertParamIsEq<Hash>;
                }
            }
        }
        #[automatically_derived]
        #[allow(unused_qualifications)]
        impl ::std::fmt::Debug for Statement {
            fn fmt(&self, f: &mut ::std::fmt::Formatter)
             -> ::std::fmt::Result {
                match (&*self,) {
                    (&Statement::Candidate(ref __self_0),) => {
                        let mut debug_trait_builder =
                            f.debug_tuple("Candidate");
                        let _ = debug_trait_builder.field(&&(*__self_0));
                        debug_trait_builder.finish()
                    }
                    (&Statement::Valid(ref __self_0),) => {
                        let mut debug_trait_builder = f.debug_tuple("Valid");
                        let _ = debug_trait_builder.field(&&(*__self_0));
                        debug_trait_builder.finish()
                    }
                    (&Statement::Invalid(ref __self_0),) => {
                        let mut debug_trait_builder =
                            f.debug_tuple("Invalid");
                        let _ = debug_trait_builder.field(&&(*__self_0));
                        debug_trait_builder.finish()
                    }
                    (&Statement::Available(ref __self_0),) => {
                        let mut debug_trait_builder =
                            f.debug_tuple("Available");
                        let _ = debug_trait_builder.field(&&(*__self_0));
                        debug_trait_builder.finish()
                    }
                }
            }
        }
        impl Slicable for Statement {
            fn encode(&self) -> Vec<u8> {
                let mut v = Vec::new();
                match *self {
                    Statement::Candidate(ref candidate) => {
                        v.push(StatementKind::Candidate as u8);
                        candidate.using_encoded(|s| v.extend(s));
                    }
                    Statement::Valid(ref hash) => {
                        v.push(StatementKind::Valid as u8);
                        hash.using_encoded(|s| v.extend(s));
                    }
                    Statement::Invalid(ref hash) => {
                        v.push(StatementKind::Invalid as u8);
                        hash.using_encoded(|s| v.extend(s));
                    }
                    Statement::Available(ref hash) => {
                        v.push(StatementKind::Available as u8);
                        hash.using_encoded(|s| v.extend(s));
                    }
                }
                v
            }
            fn decode<I: Input>(value: &mut I) -> Option<Self> {
                match value.read_byte() {
                    Some(x) if x == StatementKind::Candidate as u8 => {
                        Slicable::decode(value).map(Statement::Candidate)
                    }
                    Some(x) if x == StatementKind::Valid as u8 => {
                        Slicable::decode(value).map(Statement::Valid)
                    }
                    Some(x) if x == StatementKind::Invalid as u8 => {
                        Slicable::decode(value).map(Statement::Invalid)
                    }
                    Some(x) if x == StatementKind::Available as u8 => {
                        Slicable::decode(value).map(Statement::Available)
                    }
                    _ => None,
                }
            }
        }
    }
}
mod parachains {
    //! Main parachains logic. For now this is just the determination of which validators do what.
    use primitives;
    use rstd::prelude::*;
    use codec::{Slicable, Joiner};
    use runtime_support::Hashable;
    use runtime_primitives::traits::{Executable, RefInto, MaybeEmpty};
    use primitives::parachain::{Id, Chain, DutyRoster, CandidateReceipt};
    use {system, session};
    use substrate_runtime_support::{StorageValue, StorageMap};
    use substrate_runtime_support::dispatch::Result;
    #[cfg(any(feature = "std", test))]
    use rstd::marker::PhantomData;
    #[cfg(any(feature = "std", test))]
    use {runtime_io, runtime_primitives};
    pub trait Trait: system::Trait<Hash = primitives::Hash> + session::Trait {
        /// The position of the set_heads call in the block.
        const
        SET_POSITION:
        u32;
        type
        PublicAux: RefInto<Self::AccountId> +
        MaybeEmpty;
    }
    #[cfg(feature = "std")]
    #[doc = r" Parachains module."]
    pub struct Module<T: Trait>(::std::marker::PhantomData<T>);
    #[cfg(feature = "std")]
    #[doc = r" Call type for parachains."]
    pub enum Call<T: Trait> {
        __PhantomItem(::std::marker::PhantomData<T>),

        #[allow(non_camel_case_types)]
        set_heads(Vec<CandidateReceipt>),
    }
    #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
    const _IMPL_SERIALIZE_FOR_Call: () =
        {
            extern crate serde as _serde;
            #[allow(unused_macros)]
            macro_rules! try(( $ __expr : expr ) => {
                             match $ __expr {
                             _serde :: export :: Ok ( __val ) => __val ,
                             _serde :: export :: Err ( __err ) => {
                             return _serde :: export :: Err ( __err ) ; } }
                             });
            #[automatically_derived]
            impl <T: Trait> _serde::Serialize for Call<T> {
                fn serialize<__S>(&self, __serializer: __S)
                 -> _serde::export::Result<__S::Ok, __S::Error> where
                 __S: _serde::Serializer {
                    match *self {
                        Call::__PhantomItem(ref __field0) =>
                        _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                      "Call",
                                                                      0u32,
                                                                      "__PhantomItem",
                                                                      __field0),
                        Call::set_heads(ref __field0) =>
                        _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                      "Call",
                                                                      1u32,
                                                                      "set_heads",
                                                                      __field0),
                    }
                }
            }
        };
    #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
    const _IMPL_DESERIALIZE_FOR_Call: () =
        {
            extern crate serde as _serde;
            #[allow(unused_macros)]
            macro_rules! try(( $ __expr : expr ) => {
                             match $ __expr {
                             _serde :: export :: Ok ( __val ) => __val ,
                             _serde :: export :: Err ( __err ) => {
                             return _serde :: export :: Err ( __err ) ; } }
                             });
            #[automatically_derived]
            impl <'de, T: Trait> _serde::Deserialize<'de> for Call<T> {
                fn deserialize<__D>(__deserializer: __D)
                 -> _serde::export::Result<Self, __D::Error> where
                 __D: _serde::Deserializer<'de> {
                    #[allow(non_camel_case_types)]
                    enum __Field { __field0, __field1, }
                    struct __FieldVisitor;
                    impl <'de> _serde::de::Visitor<'de> for __FieldVisitor {
                        type
                        Value
                        =
                        __Field;
                        fn expecting(&self,
                                     __formatter:
                                         &mut _serde::export::Formatter)
                         -> _serde::export::fmt::Result {
                            _serde::export::Formatter::write_str(__formatter,
                                                                 "variant identifier")
                        }
                        fn visit_u64<__E>(self, __value: u64)
                         -> _serde::export::Result<Self::Value, __E> where
                         __E: _serde::de::Error {
                            match __value {
                                0u64 => _serde::export::Ok(__Field::__field0),
                                1u64 => _serde::export::Ok(__Field::__field1),
                                _ =>
                                _serde::export::Err(_serde::de::Error::invalid_value(_serde::de::Unexpected::Unsigned(__value),
                                                                                     &"variant index 0 <= i < 2")),
                            }
                        }
                        fn visit_str<__E>(self, __value: &str)
                         -> _serde::export::Result<Self::Value, __E> where
                         __E: _serde::de::Error {
                            match __value {
                                "__PhantomItem" =>
                                _serde::export::Ok(__Field::__field0),
                                "set_heads" =>
                                _serde::export::Ok(__Field::__field1),
                                _ => {
                                    _serde::export::Err(_serde::de::Error::unknown_variant(__value,
                                                                                           VARIANTS))
                                }
                            }
                        }
                        fn visit_bytes<__E>(self, __value: &[u8])
                         -> _serde::export::Result<Self::Value, __E> where
                         __E: _serde::de::Error {
                            match __value {
                                b"__PhantomItem" =>
                                _serde::export::Ok(__Field::__field0),
                                b"set_heads" =>
                                _serde::export::Ok(__Field::__field1),
                                _ => {
                                    let __value =
                                        &_serde::export::from_utf8_lossy(__value);
                                    _serde::export::Err(_serde::de::Error::unknown_variant(__value,
                                                                                           VARIANTS))
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
                    struct __Visitor<'de, T: Trait> {
                        marker: _serde::export::PhantomData<Call<T>>,
                        lifetime: _serde::export::PhantomData<&'de ()>,
                    }
                    impl <'de, T: Trait> _serde::de::Visitor<'de> for
                     __Visitor<'de, T> {
                        type
                        Value
                        =
                        Call<T>;
                        fn expecting(&self,
                                     __formatter:
                                         &mut _serde::export::Formatter)
                         -> _serde::export::fmt::Result {
                            _serde::export::Formatter::write_str(__formatter,
                                                                 "enum Call")
                        }
                        fn visit_enum<__A>(self, __data: __A)
                         -> _serde::export::Result<Self::Value, __A::Error>
                         where __A: _serde::de::EnumAccess<'de> {
                            match match _serde::de::EnumAccess::variant(__data)
                                      {
                                      _serde::export::Ok(__val) => __val,
                                      _serde::export::Err(__err) => {
                                          return _serde::export::Err(__err);
                                      }
                                  } {
                                (__Field::__field0, __variant) =>
                                _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<::std::marker::PhantomData<T>>(__variant),
                                                            Call::__PhantomItem),
                                (__Field::__field1, __variant) =>
                                _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<Vec<CandidateReceipt>>(__variant),
                                                            Call::set_heads),
                            }
                        }
                    }
                    const VARIANTS: &'static [&'static str] =
                        &["__PhantomItem", "set_heads"];
                    _serde::Deserializer::deserialize_enum(__deserializer,
                                                           "Call", VARIANTS,
                                                           __Visitor{marker:
                                                                         _serde::export::PhantomData::<Call<T>>,
                                                                     lifetime:
                                                                         _serde::export::PhantomData,})
                }
            }
        };
    impl <T: Trait> ::dispatch::Clone for Call<T> {
        fn clone(&self) -> Self {
            match *self {
                Call::set_heads(ref heads) => Call::set_heads(heads.clone()),
                Call::__PhantomItem(_) => {
                    {
                        ::rt::begin_panic("internal error: entered unreachable code",
                                          &("polkadot/runtime/src/parachains.rs",
                                            44u32, 1u32))
                    }
                }
            }
        }
    }
    impl <T: Trait> ::dispatch::PartialEq for Call<T> {
        fn eq(&self, other: &Self) -> bool {
            match *self {
                Call::set_heads(ref heads) => {
                    let self_params = (heads,);
                    if let Call::set_heads(ref heads) = *other {
                        self_params == (heads,)
                    } else {
                        if let Call::__PhantomItem(_) = *other {
                            {
                                {
                                    ::rt::begin_panic("internal error: entered unreachable code",
                                                      &("polkadot/runtime/src/parachains.rs",
                                                        44u32, 1u32))
                                }
                            }
                        } else { false }
                    }
                }
                Call::__PhantomItem(_) => {
                    {
                        ::rt::begin_panic("internal error: entered unreachable code",
                                          &("polkadot/runtime/src/parachains.rs",
                                            44u32, 1u32))
                    }
                }
            }
        }
    }
    impl <T: Trait> ::dispatch::Eq for Call<T> { }
    #[cfg(feature = "std")]
    impl <T: Trait> ::dispatch::fmt::Debug for Call<T> {
        fn fmt(&self, f: &mut ::dispatch::fmt::Formatter)
         -> ::dispatch::result::Result<(), ::dispatch::fmt::Error> {
            match *self {
                Call::set_heads(ref heads) =>
                f.write_fmt(::std::fmt::Arguments::new_v1_formatted(&["", ""],
                                                                    &match (&"set_heads",
                                                                            &(heads.clone(),))
                                                                         {
                                                                         (arg0,
                                                                          arg1)
                                                                         =>
                                                                         [::std::fmt::ArgumentV1::new(arg0,
                                                                                                      ::std::fmt::Display::fmt),
                                                                          ::std::fmt::ArgumentV1::new(arg1,
                                                                                                      ::std::fmt::Debug::fmt)],
                                                                     },
                                                                    &[::std::fmt::rt::v1::Argument{position:
                                                                                                       ::std::fmt::rt::v1::Position::At(0usize),
                                                                                                   format:
                                                                                                       ::std::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                          ' ',
                                                                                                                                      align:
                                                                                                                                          ::std::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                      flags:
                                                                                                                                          0u32,
                                                                                                                                      precision:
                                                                                                                                          ::std::fmt::rt::v1::Count::Implied,
                                                                                                                                      width:
                                                                                                                                          ::std::fmt::rt::v1::Count::Implied,},},
                                                                      ::std::fmt::rt::v1::Argument{position:
                                                                                                       ::std::fmt::rt::v1::Position::At(1usize),
                                                                                                   format:
                                                                                                       ::std::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                          ' ',
                                                                                                                                      align:
                                                                                                                                          ::std::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                      flags:
                                                                                                                                          0u32,
                                                                                                                                      precision:
                                                                                                                                          ::std::fmt::rt::v1::Count::Implied,
                                                                                                                                      width:
                                                                                                                                          ::std::fmt::rt::v1::Count::Implied,},}])),
                Call::__PhantomItem(_) => {
                    {
                        ::rt::begin_panic("internal error: entered unreachable code",
                                          &("polkadot/runtime/src/parachains.rs",
                                            44u32, 1u32))
                    }
                }
            }
        }
    }
    impl <T: Trait> ::dispatch::Slicable for Call<T> {
        fn decode<I: ::dispatch::Input>(input: &mut I) -> Option<Self> {
            match input.read_byte()? {
                0 => {
                    let heads = ::dispatch::Slicable::decode(input)?;
                    Some(Call::set_heads(heads))
                }
                _ => None,
            }
        }
        fn encode(&self) -> ::dispatch::Vec<u8> {
            let mut v = ::dispatch::Vec::new();
            match *self {
                Call::set_heads(ref heads) => {
                    v.push(0 as u8);
                    heads.using_encoded(|s| v.extend(s));
                }
                Call::__PhantomItem(_) => {
                    {
                        ::rt::begin_panic("internal error: entered unreachable code",
                                          &("polkadot/runtime/src/parachains.rs",
                                            44u32, 1u32))
                    }
                }
            }
            v
        }
        fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
            f(self.encode().as_slice())
        }
    }
    impl <T: Trait> ::dispatch::AuxDispatchable for Call<T> {
        type
        Trait
        =
        T;
        type
        Aux
        =
        <T as Trait>::PublicAux;
        fn dispatch(self, aux: &Self::Aux) -> ::dispatch::Result {
            match self {
                Call::set_heads(heads) => <Module<T>>::set_heads(aux, heads),
                Call::__PhantomItem(_) => {
                    {
                        ::rt::begin_panic("__PhantomItem should never be used.",
                                          &("polkadot/runtime/src/parachains.rs",
                                            44u32, 1u32))
                    }
                }
            }
        }
    }
    impl <T: Trait> ::dispatch::AuxCallable for Module<T> {
        type
        Call
        =
        Call<T>;
    }
    impl <T: Trait> Module<T> {
        pub fn aux_dispatch<D: ::dispatch::AuxDispatchable<Trait =
                            T>>(d: D, aux: &D::Aux) -> ::dispatch::Result {
            d.dispatch(aux)
        }
        pub fn dispatch<D: ::dispatch::Dispatchable<Trait = T>>(d: D)
         -> ::dispatch::Result {
            d.dispatch()
        }
    }
    pub struct Parachains<T: Trait>(::storage::generator::PhantomData<T>);
    impl <T: Trait> ::storage::generator::StorageValue<Vec<Id>> for
     Parachains<T> {
        type
        Query
        =
        Vec<Id>;
        /// Get the storage key.
        fn key() -> &'static [u8] { b"para:chains" }
        /// Load the value from the provided storage instance.
        fn get<S: ::GenericStorage>(storage: &S) -> Self::Query {
            storage.get_or_default(b"para:chains")
        }
        /// Take a value from storage, removing it afterwards.
        fn take<S: ::GenericStorage>(storage: &S) -> Self::Query {
            storage.take_or_default(b"para:chains")
        }
    }
    pub struct Code<T: Trait>(::storage::generator::PhantomData<T>);
    impl <T: Trait> ::storage::generator::StorageMap<Id, Vec<u8>> for Code<T>
     {
        type
        Query
        =
        Option<Vec<u8>>;
        /// Get the prefix key in storage.
        fn prefix() -> &'static [u8] { b"para:code" }
        /// Get the storage key used to fetch a value corresponding to a specific key.
        fn key_for(x: &Id) -> Vec<u8> {
            let mut key = b"para:code".to_vec();
            key.extend(::codec::Slicable::encode(x));
            key
        }
        /// Load the value associated with the given key from the map.
        fn get<S: ::GenericStorage>(key: &Id, storage: &S) -> Self::Query {
            let key =
                <Code<T> as
                    ::storage::generator::StorageMap<Id,
                                                     Vec<u8>>>::key_for(key);
            storage.get(&key[..])
        }
        /// Take the value, reading and removing it.
        fn take<S: ::GenericStorage>(key: &Id, storage: &S) -> Self::Query {
            let key =
                <Code<T> as
                    ::storage::generator::StorageMap<Id,
                                                     Vec<u8>>>::key_for(key);
            storage.take(&key[..])
        }
    }
    pub struct Heads<T: Trait>(::storage::generator::PhantomData<T>);
    impl <T: Trait> ::storage::generator::StorageMap<Id, Vec<u8>> for Heads<T>
     {
        type
        Query
        =
        Option<Vec<u8>>;
        /// Get the prefix key in storage.
        fn prefix() -> &'static [u8] { b"para:head" }
        /// Get the storage key used to fetch a value corresponding to a specific key.
        fn key_for(x: &Id) -> Vec<u8> {
            let mut key = b"para:head".to_vec();
            key.extend(::codec::Slicable::encode(x));
            key
        }
        /// Load the value associated with the given key from the map.
        fn get<S: ::GenericStorage>(key: &Id, storage: &S) -> Self::Query {
            let key =
                <Heads<T> as
                    ::storage::generator::StorageMap<Id,
                                                     Vec<u8>>>::key_for(key);
            storage.get(&key[..])
        }
        /// Take the value, reading and removing it.
        fn take<S: ::GenericStorage>(key: &Id, storage: &S) -> Self::Query {
            let key =
                <Heads<T> as
                    ::storage::generator::StorageMap<Id,
                                                     Vec<u8>>>::key_for(key);
            storage.take(&key[..])
        }
    }
    struct DidUpdate<T: Trait>(::storage::generator::PhantomData<T>);
    impl <T: Trait> ::storage::generator::StorageValue<bool> for DidUpdate<T>
     {
        type
        Query
        =
        bool;
        /// Get the storage key.
        fn key() -> &'static [u8] { b"para:did" }
        /// Load the value from the provided storage instance.
        fn get<S: ::GenericStorage>(storage: &S) -> Self::Query {
            storage.get_or_default(b"para:did")
        }
        /// Take a value from storage, removing it afterwards.
        fn take<S: ::GenericStorage>(storage: &S) -> Self::Query {
            storage.take_or_default(b"para:did")
        }
    }
    trait Store {
        type
        Parachains;
        type
        Code;
        type
        Heads;
        type
        DidUpdate;
    }
    impl <T: Trait> Store for Module<T> {
        type
        Parachains
        =
        Parachains<T>;
        type
        Code
        =
        Code<T>;
        type
        Heads
        =
        Heads<T>;
        type
        DidUpdate
        =
        DidUpdate<T>;
    }
    impl <T: Trait> Module<T> {
        pub fn active_parachains() -> Vec<Id> {
            <Parachains<T> as
                ::storage::generator::StorageValue<Vec<Id>>>::get(&::storage::RuntimeStorage)
        }
        pub fn parachain_code<K: ::storage::generator::Borrow<Id>>(key: K)
         -> Option<Vec<u8>> {
            <Code<T> as
                ::storage::generator::StorageMap<Id,
                                                 Vec<u8>>>::get(key.borrow(),
                                                                &::storage::RuntimeStorage)
        }
        pub fn parachain_head<K: ::storage::generator::Borrow<Id>>(key: K)
         -> Option<Vec<u8>> {
            <Heads<T> as
                ::storage::generator::StorageMap<Id,
                                                 Vec<u8>>>::get(key.borrow(),
                                                                &::storage::RuntimeStorage)
        }
    }
    impl <T: Trait> Module<T> {
        /// Calculate the current block's duty roster using system's random seed.
        pub fn calculate_duty_roster() -> DutyRoster {
            let parachains = Self::active_parachains();
            let parachain_count = parachains.len();
            let validator_count =
                <session::Module<T>>::validator_count() as usize;
            let validators_per_parachain =
                if parachain_count != 0 {
                    (validator_count - 1) / parachain_count
                } else { 0 };
            let mut roles_val =
                (0..validator_count).map(|i|
                                             match i {
                                                 i if
                                                 i <
                                                     parachain_count *
                                                         validators_per_parachain
                                                 => {
                                                     let idx =
                                                         i /
                                                             validators_per_parachain;
                                                     Chain::Parachain(parachains[idx].clone())
                                                 }
                                                 _ => Chain::Relay,
                                             }).collect::<Vec<_>>();
            let mut roles_gua = roles_val.clone();
            let random_seed = system::Module::<T>::random_seed();
            let mut seed =
                random_seed.to_vec().and(b"validator_role_pairs").blake2_256();
            for i in 0..(validator_count - 1) {
                let offset = (i * 8 % 32) as usize;
                let remaining = (validator_count - i) as usize;
                let val_index =
                    u32::decode(&mut &seed[offset..offset +
                                                       4]).expect("using 4 bytes for a 32-bit quantity")
                        as usize % remaining;
                let gua_index =
                    u32::decode(&mut &seed[offset +
                                               4..offset +
                                                      8]).expect("using 4 bytes for a 32-bit quantity")
                        as usize % remaining;
                if offset == 24 { seed = seed.blake2_256(); }
                roles_val.swap(remaining - 1, val_index);
                roles_gua.swap(remaining - 1, gua_index);
            }
            DutyRoster{validator_duty: roles_val, guarantor_duty: roles_gua,}
        }
        /// Register a parachain with given code.
        /// Fails if given ID is already used.
        pub fn register_parachain(id: Id, code: Vec<u8>,
                                  initial_head_data: Vec<u8>) {
            let mut parachains = Self::active_parachains();
            match parachains.binary_search(&id) {
                Ok(_) => {
                    ::rt::begin_panic_fmt(&::std::fmt::Arguments::new_v1_formatted(&["Parachain with id ",
                                                                                     " already exists"],
                                                                                   &match (&id.into_inner(),)
                                                                                        {
                                                                                        (arg0,)
                                                                                        =>
                                                                                        [::std::fmt::ArgumentV1::new(arg0,
                                                                                                                     ::std::fmt::Display::fmt)],
                                                                                    },
                                                                                   &[::std::fmt::rt::v1::Argument{position:
                                                                                                                      ::std::fmt::rt::v1::Position::At(0usize),
                                                                                                                  format:
                                                                                                                      ::std::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                         ' ',
                                                                                                                                                     align:
                                                                                                                                                         ::std::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                     flags:
                                                                                                                                                         0u32,
                                                                                                                                                     precision:
                                                                                                                                                         ::std::fmt::rt::v1::Count::Implied,
                                                                                                                                                     width:
                                                                                                                                                         ::std::fmt::rt::v1::Count::Implied,},}]),
                                          &("polkadot/runtime/src/parachains.rs",
                                            123u32, 13u32))
                }
                Err(idx) => parachains.insert(idx, id),
            }
            <Code<T>>::insert(id, code);
            <Parachains<T>>::put(parachains);
            <Heads<T>>::insert(id, initial_head_data);
        }
        /// Deregister a parachain with given id
        pub fn deregister_parachain(id: Id) {
            let mut parachains = Self::active_parachains();
            match parachains.binary_search(&id) {
                Ok(idx) => { parachains.remove(idx); }
                Err(_) => { }
            }
            <Code<T>>::remove(id);
            <Heads<T>>::remove(id);
            <Parachains<T>>::put(parachains);
        }
        fn set_heads(aux: &<T as Trait>::PublicAux,
                     heads: Vec<CandidateReceipt>) -> Result {
            {
                if !aux.is_empty() {
                    { return Err("set_heads must not be signed"); };
                }
            };
            {
                if !!<DidUpdate<T>>::exists() {
                    {
                        return Err("Parachain heads must be updated only once in the block");
                    };
                }
            };
            {
                if !(<system::Module<T>>::extrinsic_index() ==
                         T::SET_POSITION) {
                    {
                        return Err("Parachain heads update extrinsic must be at position {} in the block");
                    };
                }
            };
            let active_parachains = Self::active_parachains();
            let mut iter = active_parachains.iter();
            for head in &heads {
                {
                    if !iter.find(|&p| p == &head.parachain_index).is_some() {
                        {
                            return Err("Submitted candidate for unregistered or out-of-order parachain {}");
                        };
                    }
                };
            }
            for head in heads {
                let id = head.parachain_index.clone();
                <Heads<T>>::insert(id, head.head_data.0);
            }
            <DidUpdate<T>>::put(true);
            Ok(())
        }
    }
    impl <T: Trait> Executable for Module<T> {
        fn execute() {
            if !<Self as Store>::take() {
                {
                    ::rt::begin_panic("Parachain heads must be updated once in the block",
                                      &("polkadot/runtime/src/parachains.rs",
                                        179u32, 3u32))
                }
            };
        }
    }
    /// Parachains module genesis configuration.
    #[cfg(any(feature = "std", test))]
    pub struct GenesisConfig<T: Trait> {
        /// The initial parachains, mapped to code.
        pub parachains: Vec<(Id, Vec<u8>)>,
        /// Phantom data.
        pub phantom: PhantomData<T>,
    }
    #[cfg(any(feature = "std", test))]
    impl <T: Trait> Default for GenesisConfig<T> {
        fn default() -> Self {
            GenesisConfig{parachains: Vec::new(), phantom: PhantomData,}
        }
    }
    #[cfg(any(feature = "std", test))]
    impl <T: Trait> runtime_primitives::BuildExternalities for
     GenesisConfig<T> {
        fn build_externalities(mut self) -> runtime_io::TestExternalities {
            use std::collections::HashMap;
            use runtime_io::twox_128;
            use codec::Slicable;
            self.parachains.sort_unstable_by_key(|&(ref id, _)| id.clone());
            self.parachains.dedup_by_key(|&mut (ref id, _)| id.clone());
            let only_ids: Vec<_> =
                self.parachains.iter().map(|&(ref id, _)|
                                               id).cloned().collect();
            let mut map: HashMap<_, _> =
                <[_]>::into_vec(box
                                    [(twox_128(<Parachains<T>>::key()).to_vec(),
                                      only_ids.encode())]).into_iter().collect();
            for (id, code) in self.parachains {
                let key = twox_128(&<Code<T>>::key_for(&id)).to_vec();
                map.insert(key, code.encode());
            }
            map.into()
        }
    }
}
use primitives::{AccountId, Balance, BlockNumber, Hash, Index, Log,
                 SessionKey};
use runtime_primitives::{generic,
                         traits::{HasPublicAux, BlakeTwo256, Convert}};
#[cfg(feature = "std")]
pub use runtime_primitives::BuildExternalities;
pub use consensus::Call as ConsensusCall;
pub use timestamp::Call as TimestampCall;
pub use parachains::Call as ParachainsCall;
pub use primitives::{Header, Block, UncheckedExtrinsic, Extrinsic};
/// The position of the timestamp set extrinsic.
pub const TIMESTAMP_SET_POSITION: u32 = 0;
/// The position of the parachains set extrinsic.
pub const PARACHAINS_SET_POSITION: u32 = 1;
/// Concrete runtime type used to parameterize the various modules.
pub struct Concrete;
impl HasPublicAux for Concrete {
    type
    PublicAux
    =
    AccountId;
}
impl system::Trait for Concrete {
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
    Header
    =
    Header;
}
/// System module for this concrete runtime.
pub type System = system::Module<Concrete>;
impl consensus::Trait for Concrete {
    type
    PublicAux
    =
    <Concrete as HasPublicAux>::PublicAux;
    type
    SessionKey
    =
    SessionKey;
}
/// Consensus module for this concrete runtime.
pub type Consensus = consensus::Module<Concrete>;
impl timestamp::Trait for Concrete {
    const
    SET_POSITION:
    u32
    =
    TIMESTAMP_SET_POSITION;
    type
    Value
    =
    u64;
}
/// Timestamp module for this concrete runtime.
pub type Timestamp = timestamp::Module<Concrete>;
/// Session key conversion.
pub struct SessionKeyConversion;
impl Convert<AccountId, SessionKey> for SessionKeyConversion {
    fn convert(a: AccountId) -> SessionKey { a.0 }
}
impl session::Trait for Concrete {
    type
    ConvertAccountIdToSessionKey
    =
    SessionKeyConversion;
}
/// Session module for this concrete runtime.
pub type Session = session::Module<Concrete>;
impl staking::Trait for Concrete {
    type
    Balance
    =
    Balance;
    type
    DetermineContractAddress
    =
    BlakeTwo256;
}
/// Staking module for this concrete runtime.
pub type Staking = staking::Module<Concrete>;
impl democracy::Trait for Concrete {
    type
    Proposal
    =
    PrivCall;
}
/// Democracy module for this concrete runtime.
pub type Democracy = democracy::Module<Concrete>;
impl council::Trait for Concrete { }
/// Council module for this concrete runtime.
pub type Council = council::Module<Concrete>;
/// Council voting module for this concrete runtime.
pub type CouncilVoting = council::voting::Module<Concrete>;
impl parachains::Trait for Concrete {
    const
    SET_POSITION:
    u32
    =
    PARACHAINS_SET_POSITION;
    type
    PublicAux
    =
    <Concrete as HasPublicAux>::PublicAux;
}
pub type Parachains = parachains::Module<Concrete>;
#[doc = r" Call type for polkadot transactions."]
#[structural_match]
pub enum Call {
    Consensus(<Consensus as ::dispatch::AuxCallable>::Call),
    Session(<Session as ::dispatch::AuxCallable>::Call),
    Staking(<Staking as ::dispatch::AuxCallable>::Call),
    Timestamp(<Timestamp as ::dispatch::AuxCallable>::Call),
    Democracy(<Democracy as ::dispatch::AuxCallable>::Call),
    Council(<Council as ::dispatch::AuxCallable>::Call),
    CouncilVoting(<CouncilVoting as ::dispatch::AuxCallable>::Call),
    Parachains(<Parachains as ::dispatch::AuxCallable>::Call),
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::std::clone::Clone for Call {
    #[inline]
    fn clone(&self) -> Call {
        match (&*self,) {
            (&Call::Consensus(ref __self_0),) =>
            Call::Consensus(::std::clone::Clone::clone(&(*__self_0))),
            (&Call::Session(ref __self_0),) =>
            Call::Session(::std::clone::Clone::clone(&(*__self_0))),
            (&Call::Staking(ref __self_0),) =>
            Call::Staking(::std::clone::Clone::clone(&(*__self_0))),
            (&Call::Timestamp(ref __self_0),) =>
            Call::Timestamp(::std::clone::Clone::clone(&(*__self_0))),
            (&Call::Democracy(ref __self_0),) =>
            Call::Democracy(::std::clone::Clone::clone(&(*__self_0))),
            (&Call::Council(ref __self_0),) =>
            Call::Council(::std::clone::Clone::clone(&(*__self_0))),
            (&Call::CouncilVoting(ref __self_0),) =>
            Call::CouncilVoting(::std::clone::Clone::clone(&(*__self_0))),
            (&Call::Parachains(ref __self_0),) =>
            Call::Parachains(::std::clone::Clone::clone(&(*__self_0))),
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::std::cmp::PartialEq for Call {
    #[inline]
    fn eq(&self, other: &Call) -> bool {
        {
            let __self_vi =
                unsafe { ::std::intrinsics::discriminant_value(&*self) } as
                    isize;
            let __arg_1_vi =
                unsafe { ::std::intrinsics::discriminant_value(&*other) } as
                    isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&Call::Consensus(ref __self_0),
                     &Call::Consensus(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::Session(ref __self_0),
                     &Call::Session(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::Staking(ref __self_0),
                     &Call::Staking(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&Call::Timestamp(ref __self_0),
                     &Call::Timestamp(ref __arg_1_0)) =>
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
                    (&Call::Parachains(ref __self_0),
                     &Call::Parachains(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    _ => unsafe { ::std::intrinsics::unreachable() }
                }
            } else { false }
        }
    }
    #[inline]
    fn ne(&self, other: &Call) -> bool {
        {
            let __self_vi =
                unsafe { ::std::intrinsics::discriminant_value(&*self) } as
                    isize;
            let __arg_1_vi =
                unsafe { ::std::intrinsics::discriminant_value(&*other) } as
                    isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&Call::Consensus(ref __self_0),
                     &Call::Consensus(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::Session(ref __self_0),
                     &Call::Session(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::Staking(ref __self_0),
                     &Call::Staking(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&Call::Timestamp(ref __self_0),
                     &Call::Timestamp(ref __arg_1_0)) =>
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
                    (&Call::Parachains(ref __self_0),
                     &Call::Parachains(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    _ => unsafe { ::std::intrinsics::unreachable() }
                }
            } else { true }
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::std::cmp::Eq for Call {
    #[inline]
    #[doc(hidden)]
    fn assert_receiver_is_total_eq(&self) -> () {
        {
            let _:
                    ::std::cmp::AssertParamIsEq<<Consensus as
                                                ::dispatch::AuxCallable>::Call>;
            let _:
                    ::std::cmp::AssertParamIsEq<<Session as
                                                ::dispatch::AuxCallable>::Call>;
            let _:
                    ::std::cmp::AssertParamIsEq<<Staking as
                                                ::dispatch::AuxCallable>::Call>;
            let _:
                    ::std::cmp::AssertParamIsEq<<Timestamp as
                                                ::dispatch::AuxCallable>::Call>;
            let _:
                    ::std::cmp::AssertParamIsEq<<Democracy as
                                                ::dispatch::AuxCallable>::Call>;
            let _:
                    ::std::cmp::AssertParamIsEq<<Council as
                                                ::dispatch::AuxCallable>::Call>;
            let _:
                    ::std::cmp::AssertParamIsEq<<CouncilVoting as
                                                ::dispatch::AuxCallable>::Call>;
            let _:
                    ::std::cmp::AssertParamIsEq<<Parachains as
                                                ::dispatch::AuxCallable>::Call>;
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::std::fmt::Debug for Call {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        match (&*self,) {
            (&Call::Consensus(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Consensus");
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
            (&Call::Timestamp(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Timestamp");
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
            (&Call::Parachains(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Parachains");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
        }
    }
}
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_SERIALIZE_FOR_Call: () =
    {
        extern crate serde as _serde;
        #[allow(unused_macros)]
        macro_rules! try(( $ __expr : expr ) => {
                         match $ __expr {
                         _serde :: export :: Ok ( __val ) => __val , _serde ::
                         export :: Err ( __err ) => {
                         return _serde :: export :: Err ( __err ) ; } } });
        #[automatically_derived]
        impl _serde::Serialize for Call {
            fn serialize<__S>(&self, __serializer: __S)
             -> _serde::export::Result<__S::Ok, __S::Error> where
             __S: _serde::Serializer {
                match *self {
                    Call::Consensus(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "Call",
                                                                  0u32,
                                                                  "Consensus",
                                                                  __field0),
                    Call::Session(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "Call",
                                                                  1u32,
                                                                  "Session",
                                                                  __field0),
                    Call::Staking(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "Call",
                                                                  2u32,
                                                                  "Staking",
                                                                  __field0),
                    Call::Timestamp(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "Call",
                                                                  3u32,
                                                                  "Timestamp",
                                                                  __field0),
                    Call::Democracy(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "Call",
                                                                  4u32,
                                                                  "Democracy",
                                                                  __field0),
                    Call::Council(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "Call",
                                                                  5u32,
                                                                  "Council",
                                                                  __field0),
                    Call::CouncilVoting(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "Call",
                                                                  6u32,
                                                                  "CouncilVoting",
                                                                  __field0),
                    Call::Parachains(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "Call",
                                                                  7u32,
                                                                  "Parachains",
                                                                  __field0),
                }
            }
        }
    };
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_DESERIALIZE_FOR_Call: () =
    {
        extern crate serde as _serde;
        #[allow(unused_macros)]
        macro_rules! try(( $ __expr : expr ) => {
                         match $ __expr {
                         _serde :: export :: Ok ( __val ) => __val , _serde ::
                         export :: Err ( __err ) => {
                         return _serde :: export :: Err ( __err ) ; } } });
        #[automatically_derived]
        impl <'de> _serde::Deserialize<'de> for Call {
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
                                                             "variant identifier")
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
                            _ =>
                            _serde::export::Err(_serde::de::Error::invalid_value(_serde::de::Unexpected::Unsigned(__value),
                                                                                 &"variant index 0 <= i < 8")),
                        }
                    }
                    fn visit_str<__E>(self, __value: &str)
                     -> _serde::export::Result<Self::Value, __E> where
                     __E: _serde::de::Error {
                        match __value {
                            "Consensus" =>
                            _serde::export::Ok(__Field::__field0),
                            "Session" =>
                            _serde::export::Ok(__Field::__field1),
                            "Staking" =>
                            _serde::export::Ok(__Field::__field2),
                            "Timestamp" =>
                            _serde::export::Ok(__Field::__field3),
                            "Democracy" =>
                            _serde::export::Ok(__Field::__field4),
                            "Council" =>
                            _serde::export::Ok(__Field::__field5),
                            "CouncilVoting" =>
                            _serde::export::Ok(__Field::__field6),
                            "Parachains" =>
                            _serde::export::Ok(__Field::__field7),
                            _ => {
                                _serde::export::Err(_serde::de::Error::unknown_variant(__value,
                                                                                       VARIANTS))
                            }
                        }
                    }
                    fn visit_bytes<__E>(self, __value: &[u8])
                     -> _serde::export::Result<Self::Value, __E> where
                     __E: _serde::de::Error {
                        match __value {
                            b"Consensus" =>
                            _serde::export::Ok(__Field::__field0),
                            b"Session" =>
                            _serde::export::Ok(__Field::__field1),
                            b"Staking" =>
                            _serde::export::Ok(__Field::__field2),
                            b"Timestamp" =>
                            _serde::export::Ok(__Field::__field3),
                            b"Democracy" =>
                            _serde::export::Ok(__Field::__field4),
                            b"Council" =>
                            _serde::export::Ok(__Field::__field5),
                            b"CouncilVoting" =>
                            _serde::export::Ok(__Field::__field6),
                            b"Parachains" =>
                            _serde::export::Ok(__Field::__field7),
                            _ => {
                                let __value =
                                    &_serde::export::from_utf8_lossy(__value);
                                _serde::export::Err(_serde::de::Error::unknown_variant(__value,
                                                                                       VARIANTS))
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
                    marker: _serde::export::PhantomData<Call>,
                    lifetime: _serde::export::PhantomData<&'de ()>,
                }
                impl <'de> _serde::de::Visitor<'de> for __Visitor<'de> {
                    type
                    Value
                    =
                    Call;
                    fn expecting(&self,
                                 __formatter: &mut _serde::export::Formatter)
                     -> _serde::export::fmt::Result {
                        _serde::export::Formatter::write_str(__formatter,
                                                             "enum Call")
                    }
                    fn visit_enum<__A>(self, __data: __A)
                     -> _serde::export::Result<Self::Value, __A::Error> where
                     __A: _serde::de::EnumAccess<'de> {
                        match match _serde::de::EnumAccess::variant(__data) {
                                  _serde::export::Ok(__val) => __val,
                                  _serde::export::Err(__err) => {
                                      return _serde::export::Err(__err);
                                  }
                              } {
                            (__Field::__field0, __variant) =>
                            _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<<Consensus
                                                                                                     as
                                                                                                     ::substrate_runtime_support::dispatch>::Call>(__variant),
                                                        Call::Consensus),
                            (__Field::__field1, __variant) =>
                            _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<<Session
                                                                                                     as
                                                                                                     ::substrate_runtime_support::dispatch>::Call>(__variant),
                                                        Call::Session),
                            (__Field::__field2, __variant) =>
                            _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<<Staking
                                                                                                     as
                                                                                                     ::substrate_runtime_support::dispatch>::Call>(__variant),
                                                        Call::Staking),
                            (__Field::__field3, __variant) =>
                            _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<<Timestamp
                                                                                                     as
                                                                                                     ::substrate_runtime_support::dispatch>::Call>(__variant),
                                                        Call::Timestamp),
                            (__Field::__field4, __variant) =>
                            _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<<Democracy
                                                                                                     as
                                                                                                     ::substrate_runtime_support::dispatch>::Call>(__variant),
                                                        Call::Democracy),
                            (__Field::__field5, __variant) =>
                            _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<<Council
                                                                                                     as
                                                                                                     ::substrate_runtime_support::dispatch>::Call>(__variant),
                                                        Call::Council),
                            (__Field::__field6, __variant) =>
                            _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<<CouncilVoting
                                                                                                     as
                                                                                                     ::substrate_runtime_support::dispatch>::Call>(__variant),
                                                        Call::CouncilVoting),
                            (__Field::__field7, __variant) =>
                            _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<<Parachains
                                                                                                     as
                                                                                                     ::substrate_runtime_support::dispatch>::Call>(__variant),
                                                        Call::Parachains),
                        }
                    }
                }
                const VARIANTS: &'static [&'static str] =
                    &["Consensus", "Session", "Staking", "Timestamp",
                      "Democracy", "Council", "CouncilVoting", "Parachains"];
                _serde::Deserializer::deserialize_enum(__deserializer, "Call",
                                                       VARIANTS,
                                                       __Visitor{marker:
                                                                     _serde::export::PhantomData::<Call>,
                                                                 lifetime:
                                                                     _serde::export::PhantomData,})
            }
        }
    };
impl ::dispatch::Slicable for Call {
    fn decode<I: ::dispatch::Input>(input: &mut I) -> Option<Self> {
        match input.read_byte()? {
            0 => Some(Call::Consensus(::dispatch::Slicable::decode(input)?)),
            1 => Some(Call::Session(::dispatch::Slicable::decode(input)?)),
            2 => Some(Call::Staking(::dispatch::Slicable::decode(input)?)),
            3 => Some(Call::Timestamp(::dispatch::Slicable::decode(input)?)),
            5 => Some(Call::Democracy(::dispatch::Slicable::decode(input)?)),
            6 => Some(Call::Council(::dispatch::Slicable::decode(input)?)),
            7 =>
            Some(Call::CouncilVoting(::dispatch::Slicable::decode(input)?)),
            8 => Some(Call::Parachains(::dispatch::Slicable::decode(input)?)),
            _ => None,
        }
    }
    fn encode(&self) -> ::dispatch::Vec<u8> {
        let mut v = ::dispatch::Vec::new();
        match *self {
            Call::Consensus(ref sub) => {
                v.push(0 as u8);
                sub.using_encoded(|s| v.extend(s));
            }
            Call::Session(ref sub) => {
                v.push(1 as u8);
                sub.using_encoded(|s| v.extend(s));
            }
            Call::Staking(ref sub) => {
                v.push(2 as u8);
                sub.using_encoded(|s| v.extend(s));
            }
            Call::Timestamp(ref sub) => {
                v.push(3 as u8);
                sub.using_encoded(|s| v.extend(s));
            }
            Call::Democracy(ref sub) => {
                v.push(5 as u8);
                sub.using_encoded(|s| v.extend(s));
            }
            Call::Council(ref sub) => {
                v.push(6 as u8);
                sub.using_encoded(|s| v.extend(s));
            }
            Call::CouncilVoting(ref sub) => {
                v.push(7 as u8);
                sub.using_encoded(|s| v.extend(s));
            }
            Call::Parachains(ref sub) => {
                v.push(8 as u8);
                sub.using_encoded(|s| v.extend(s));
            }
        }
        v
    }
    fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
        f(self.encode().as_slice())
    }
}
impl ::dispatch::AuxDispatchable for Call {
    type
    Aux
    =
    <Concrete as HasPublicAux>::PublicAux;
    type
    Trait
    =
    Call;
    fn dispatch(self, aux: &<Concrete as HasPublicAux>::PublicAux)
     -> ::dispatch::Result {
        match self {
            Call::Consensus(call) => call.dispatch(&aux),
            Call::Session(call) => call.dispatch(&aux),
            Call::Staking(call) => call.dispatch(&aux),
            Call::Timestamp(call) => call.dispatch(&aux),
            Call::Democracy(call) => call.dispatch(&aux),
            Call::Council(call) => call.dispatch(&aux),
            Call::CouncilVoting(call) => call.dispatch(&aux),
            Call::Parachains(call) => call.dispatch(&aux),
        }
    }
}
impl ::dispatch::IsAuxSubType<Consensus> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Consensus as ::dispatch::AuxCallable>::Call> {
        if let Call::Consensus(ref r) = *self { Some(r) } else { None }
    }
}
impl ::dispatch::IsAuxSubType<Session> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Session as ::dispatch::AuxCallable>::Call> {
        if let Call::Session(ref r) = *self { Some(r) } else { None }
    }
}
impl ::dispatch::IsAuxSubType<Staking> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Staking as ::dispatch::AuxCallable>::Call> {
        if let Call::Staking(ref r) = *self { Some(r) } else { None }
    }
}
impl ::dispatch::IsAuxSubType<Timestamp> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Timestamp as ::dispatch::AuxCallable>::Call> {
        if let Call::Timestamp(ref r) = *self { Some(r) } else { None }
    }
}
impl ::dispatch::IsAuxSubType<Democracy> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Democracy as ::dispatch::AuxCallable>::Call> {
        if let Call::Democracy(ref r) = *self { Some(r) } else { None }
    }
}
impl ::dispatch::IsAuxSubType<Council> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Council as ::dispatch::AuxCallable>::Call> {
        if let Call::Council(ref r) = *self { Some(r) } else { None }
    }
}
impl ::dispatch::IsAuxSubType<CouncilVoting> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<CouncilVoting as ::dispatch::AuxCallable>::Call> {
        if let Call::CouncilVoting(ref r) = *self { Some(r) } else { None }
    }
}
impl ::dispatch::IsAuxSubType<Parachains> for Call {
    fn is_aux_sub_type(&self)
     -> Option<&<Parachains as ::dispatch::AuxCallable>::Call> {
        if let Call::Parachains(ref r) = *self { Some(r) } else { None }
    }
}
#[doc = r" Internal calls."]
#[structural_match]
pub enum PrivCall {
    Consensus(<Consensus as ::dispatch::Callable>::Call),
    Session(<Session as ::dispatch::Callable>::Call),
    Staking(<Staking as ::dispatch::Callable>::Call),
    Democracy(<Democracy as ::dispatch::Callable>::Call),
    Council(<Council as ::dispatch::Callable>::Call),
    CouncilVoting(<CouncilVoting as ::dispatch::Callable>::Call),
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::std::clone::Clone for PrivCall {
    #[inline]
    fn clone(&self) -> PrivCall {
        match (&*self,) {
            (&PrivCall::Consensus(ref __self_0),) =>
            PrivCall::Consensus(::std::clone::Clone::clone(&(*__self_0))),
            (&PrivCall::Session(ref __self_0),) =>
            PrivCall::Session(::std::clone::Clone::clone(&(*__self_0))),
            (&PrivCall::Staking(ref __self_0),) =>
            PrivCall::Staking(::std::clone::Clone::clone(&(*__self_0))),
            (&PrivCall::Democracy(ref __self_0),) =>
            PrivCall::Democracy(::std::clone::Clone::clone(&(*__self_0))),
            (&PrivCall::Council(ref __self_0),) =>
            PrivCall::Council(::std::clone::Clone::clone(&(*__self_0))),
            (&PrivCall::CouncilVoting(ref __self_0),) =>
            PrivCall::CouncilVoting(::std::clone::Clone::clone(&(*__self_0))),
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::std::cmp::PartialEq for PrivCall {
    #[inline]
    fn eq(&self, other: &PrivCall) -> bool {
        {
            let __self_vi =
                unsafe { ::std::intrinsics::discriminant_value(&*self) } as
                    isize;
            let __arg_1_vi =
                unsafe { ::std::intrinsics::discriminant_value(&*other) } as
                    isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&PrivCall::Consensus(ref __self_0),
                     &PrivCall::Consensus(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&PrivCall::Session(ref __self_0),
                     &PrivCall::Session(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&PrivCall::Staking(ref __self_0),
                     &PrivCall::Staking(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&PrivCall::Democracy(ref __self_0),
                     &PrivCall::Democracy(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&PrivCall::Council(ref __self_0),
                     &PrivCall::Council(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    (&PrivCall::CouncilVoting(ref __self_0),
                     &PrivCall::CouncilVoting(ref __arg_1_0)) =>
                    (*__self_0) == (*__arg_1_0),
                    _ => unsafe { ::std::intrinsics::unreachable() }
                }
            } else { false }
        }
    }
    #[inline]
    fn ne(&self, other: &PrivCall) -> bool {
        {
            let __self_vi =
                unsafe { ::std::intrinsics::discriminant_value(&*self) } as
                    isize;
            let __arg_1_vi =
                unsafe { ::std::intrinsics::discriminant_value(&*other) } as
                    isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&PrivCall::Consensus(ref __self_0),
                     &PrivCall::Consensus(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&PrivCall::Session(ref __self_0),
                     &PrivCall::Session(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&PrivCall::Staking(ref __self_0),
                     &PrivCall::Staking(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&PrivCall::Democracy(ref __self_0),
                     &PrivCall::Democracy(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&PrivCall::Council(ref __self_0),
                     &PrivCall::Council(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    (&PrivCall::CouncilVoting(ref __self_0),
                     &PrivCall::CouncilVoting(ref __arg_1_0)) =>
                    (*__self_0) != (*__arg_1_0),
                    _ => unsafe { ::std::intrinsics::unreachable() }
                }
            } else { true }
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::std::cmp::Eq for PrivCall {
    #[inline]
    #[doc(hidden)]
    fn assert_receiver_is_total_eq(&self) -> () {
        {
            let _:
                    ::std::cmp::AssertParamIsEq<<Consensus as
                                                ::dispatch::Callable>::Call>;
            let _:
                    ::std::cmp::AssertParamIsEq<<Session as
                                                ::dispatch::Callable>::Call>;
            let _:
                    ::std::cmp::AssertParamIsEq<<Staking as
                                                ::dispatch::Callable>::Call>;
            let _:
                    ::std::cmp::AssertParamIsEq<<Democracy as
                                                ::dispatch::Callable>::Call>;
            let _:
                    ::std::cmp::AssertParamIsEq<<Council as
                                                ::dispatch::Callable>::Call>;
            let _:
                    ::std::cmp::AssertParamIsEq<<CouncilVoting as
                                                ::dispatch::Callable>::Call>;
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::std::fmt::Debug for PrivCall {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        match (&*self,) {
            (&PrivCall::Consensus(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Consensus");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&PrivCall::Session(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Session");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&PrivCall::Staking(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Staking");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&PrivCall::Democracy(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Democracy");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&PrivCall::Council(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Council");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&PrivCall::CouncilVoting(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("CouncilVoting");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
        }
    }
}
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_SERIALIZE_FOR_PrivCall: () =
    {
        extern crate serde as _serde;
        #[allow(unused_macros)]
        macro_rules! try(( $ __expr : expr ) => {
                         match $ __expr {
                         _serde :: export :: Ok ( __val ) => __val , _serde ::
                         export :: Err ( __err ) => {
                         return _serde :: export :: Err ( __err ) ; } } });
        #[automatically_derived]
        impl _serde::Serialize for PrivCall {
            fn serialize<__S>(&self, __serializer: __S)
             -> _serde::export::Result<__S::Ok, __S::Error> where
             __S: _serde::Serializer {
                match *self {
                    PrivCall::Consensus(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "PrivCall",
                                                                  0u32,
                                                                  "Consensus",
                                                                  __field0),
                    PrivCall::Session(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "PrivCall",
                                                                  1u32,
                                                                  "Session",
                                                                  __field0),
                    PrivCall::Staking(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "PrivCall",
                                                                  2u32,
                                                                  "Staking",
                                                                  __field0),
                    PrivCall::Democracy(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "PrivCall",
                                                                  3u32,
                                                                  "Democracy",
                                                                  __field0),
                    PrivCall::Council(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "PrivCall",
                                                                  4u32,
                                                                  "Council",
                                                                  __field0),
                    PrivCall::CouncilVoting(ref __field0) =>
                    _serde::Serializer::serialize_newtype_variant(__serializer,
                                                                  "PrivCall",
                                                                  5u32,
                                                                  "CouncilVoting",
                                                                  __field0),
                }
            }
        }
    };
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_DESERIALIZE_FOR_PrivCall: () =
    {
        extern crate serde as _serde;
        #[allow(unused_macros)]
        macro_rules! try(( $ __expr : expr ) => {
                         match $ __expr {
                         _serde :: export :: Ok ( __val ) => __val , _serde ::
                         export :: Err ( __err ) => {
                         return _serde :: export :: Err ( __err ) ; } } });
        #[automatically_derived]
        impl <'de> _serde::Deserialize<'de> for PrivCall {
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
                                                             "variant identifier")
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
                            _ =>
                            _serde::export::Err(_serde::de::Error::invalid_value(_serde::de::Unexpected::Unsigned(__value),
                                                                                 &"variant index 0 <= i < 6")),
                        }
                    }
                    fn visit_str<__E>(self, __value: &str)
                     -> _serde::export::Result<Self::Value, __E> where
                     __E: _serde::de::Error {
                        match __value {
                            "Consensus" =>
                            _serde::export::Ok(__Field::__field0),
                            "Session" =>
                            _serde::export::Ok(__Field::__field1),
                            "Staking" =>
                            _serde::export::Ok(__Field::__field2),
                            "Democracy" =>
                            _serde::export::Ok(__Field::__field3),
                            "Council" =>
                            _serde::export::Ok(__Field::__field4),
                            "CouncilVoting" =>
                            _serde::export::Ok(__Field::__field5),
                            _ => {
                                _serde::export::Err(_serde::de::Error::unknown_variant(__value,
                                                                                       VARIANTS))
                            }
                        }
                    }
                    fn visit_bytes<__E>(self, __value: &[u8])
                     -> _serde::export::Result<Self::Value, __E> where
                     __E: _serde::de::Error {
                        match __value {
                            b"Consensus" =>
                            _serde::export::Ok(__Field::__field0),
                            b"Session" =>
                            _serde::export::Ok(__Field::__field1),
                            b"Staking" =>
                            _serde::export::Ok(__Field::__field2),
                            b"Democracy" =>
                            _serde::export::Ok(__Field::__field3),
                            b"Council" =>
                            _serde::export::Ok(__Field::__field4),
                            b"CouncilVoting" =>
                            _serde::export::Ok(__Field::__field5),
                            _ => {
                                let __value =
                                    &_serde::export::from_utf8_lossy(__value);
                                _serde::export::Err(_serde::de::Error::unknown_variant(__value,
                                                                                       VARIANTS))
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
                    marker: _serde::export::PhantomData<PrivCall>,
                    lifetime: _serde::export::PhantomData<&'de ()>,
                }
                impl <'de> _serde::de::Visitor<'de> for __Visitor<'de> {
                    type
                    Value
                    =
                    PrivCall;
                    fn expecting(&self,
                                 __formatter: &mut _serde::export::Formatter)
                     -> _serde::export::fmt::Result {
                        _serde::export::Formatter::write_str(__formatter,
                                                             "enum PrivCall")
                    }
                    fn visit_enum<__A>(self, __data: __A)
                     -> _serde::export::Result<Self::Value, __A::Error> where
                     __A: _serde::de::EnumAccess<'de> {
                        match match _serde::de::EnumAccess::variant(__data) {
                                  _serde::export::Ok(__val) => __val,
                                  _serde::export::Err(__err) => {
                                      return _serde::export::Err(__err);
                                  }
                              } {
                            (__Field::__field0, __variant) =>
                            _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<<Consensus
                                                                                                     as
                                                                                                     ::substrate_runtime_support::dispatch>::Call>(__variant),
                                                        PrivCall::Consensus),
                            (__Field::__field1, __variant) =>
                            _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<<Session
                                                                                                     as
                                                                                                     ::substrate_runtime_support::dispatch>::Call>(__variant),
                                                        PrivCall::Session),
                            (__Field::__field2, __variant) =>
                            _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<<Staking
                                                                                                     as
                                                                                                     ::substrate_runtime_support::dispatch>::Call>(__variant),
                                                        PrivCall::Staking),
                            (__Field::__field3, __variant) =>
                            _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<<Democracy
                                                                                                     as
                                                                                                     ::substrate_runtime_support::dispatch>::Call>(__variant),
                                                        PrivCall::Democracy),
                            (__Field::__field4, __variant) =>
                            _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<<Council
                                                                                                     as
                                                                                                     ::substrate_runtime_support::dispatch>::Call>(__variant),
                                                        PrivCall::Council),
                            (__Field::__field5, __variant) =>
                            _serde::export::Result::map(_serde::de::VariantAccess::newtype_variant::<<CouncilVoting
                                                                                                     as
                                                                                                     ::substrate_runtime_support::dispatch>::Call>(__variant),
                                                        PrivCall::CouncilVoting),
                        }
                    }
                }
                const VARIANTS: &'static [&'static str] =
                    &["Consensus", "Session", "Staking", "Democracy",
                      "Council", "CouncilVoting"];
                _serde::Deserializer::deserialize_enum(__deserializer,
                                                       "PrivCall", VARIANTS,
                                                       __Visitor{marker:
                                                                     _serde::export::PhantomData::<PrivCall>,
                                                                 lifetime:
                                                                     _serde::export::PhantomData,})
            }
        }
    };
impl ::dispatch::Slicable for PrivCall {
    fn decode<I: ::dispatch::Input>(input: &mut I) -> Option<Self> {
        match input.read_byte()? {
            0 =>
            Some(PrivCall::Consensus(::dispatch::Slicable::decode(input)?)),
            1 =>
            Some(PrivCall::Session(::dispatch::Slicable::decode(input)?)),
            2 =>
            Some(PrivCall::Staking(::dispatch::Slicable::decode(input)?)),
            5 =>
            Some(PrivCall::Democracy(::dispatch::Slicable::decode(input)?)),
            6 =>
            Some(PrivCall::Council(::dispatch::Slicable::decode(input)?)),
            7 =>
            Some(PrivCall::CouncilVoting(::dispatch::Slicable::decode(input)?)),
            _ => None,
        }
    }
    fn encode(&self) -> ::dispatch::Vec<u8> {
        let mut v = ::dispatch::Vec::new();
        match *self {
            PrivCall::Consensus(ref sub) => {
                v.push(0 as u8);
                sub.using_encoded(|s| v.extend(s));
            }
            PrivCall::Session(ref sub) => {
                v.push(1 as u8);
                sub.using_encoded(|s| v.extend(s));
            }
            PrivCall::Staking(ref sub) => {
                v.push(2 as u8);
                sub.using_encoded(|s| v.extend(s));
            }
            PrivCall::Democracy(ref sub) => {
                v.push(5 as u8);
                sub.using_encoded(|s| v.extend(s));
            }
            PrivCall::Council(ref sub) => {
                v.push(6 as u8);
                sub.using_encoded(|s| v.extend(s));
            }
            PrivCall::CouncilVoting(ref sub) => {
                v.push(7 as u8);
                sub.using_encoded(|s| v.extend(s));
            }
        }
        v
    }
    fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
        f(self.encode().as_slice())
    }
}
impl ::dispatch::Dispatchable for PrivCall {
    type
    Trait
    =
    PrivCall;
    fn dispatch(self) -> ::dispatch::Result {
        match self {
            PrivCall::Consensus(call) => call.dispatch(),
            PrivCall::Session(call) => call.dispatch(),
            PrivCall::Staking(call) => call.dispatch(),
            PrivCall::Democracy(call) => call.dispatch(),
            PrivCall::Council(call) => call.dispatch(),
            PrivCall::CouncilVoting(call) => call.dispatch(),
        }
    }
}
impl ::dispatch::IsSubType<Consensus> for PrivCall {
    fn is_sub_type(&self)
     -> Option<&<Consensus as ::dispatch::Callable>::Call> {
        if let PrivCall::Consensus(ref r) = *self { Some(r) } else { None }
    }
}
impl ::dispatch::IsSubType<Session> for PrivCall {
    fn is_sub_type(&self)
     -> Option<&<Session as ::dispatch::Callable>::Call> {
        if let PrivCall::Session(ref r) = *self { Some(r) } else { None }
    }
}
impl ::dispatch::IsSubType<Staking> for PrivCall {
    fn is_sub_type(&self)
     -> Option<&<Staking as ::dispatch::Callable>::Call> {
        if let PrivCall::Staking(ref r) = *self { Some(r) } else { None }
    }
}
impl ::dispatch::IsSubType<Democracy> for PrivCall {
    fn is_sub_type(&self)
     -> Option<&<Democracy as ::dispatch::Callable>::Call> {
        if let PrivCall::Democracy(ref r) = *self { Some(r) } else { None }
    }
}
impl ::dispatch::IsSubType<Council> for PrivCall {
    fn is_sub_type(&self)
     -> Option<&<Council as ::dispatch::Callable>::Call> {
        if let PrivCall::Council(ref r) = *self { Some(r) } else { None }
    }
}
impl ::dispatch::IsSubType<CouncilVoting> for PrivCall {
    fn is_sub_type(&self)
     -> Option<&<CouncilVoting as ::dispatch::Callable>::Call> {
        if let PrivCall::CouncilVoting(ref r) = *self {
            Some(r)
        } else { None }
    }
}
/// Executive: handles dispatch to the various modules.
pub type Executive =
    executive::Executive<Concrete, Block, Staking,
                         (((((((), Parachains), Council), Democracy),
                            Staking), Session), Timestamp)>;
#[cfg(any(feature = "std", test))]
pub type ConsensusConfig = consensus::GenesisConfig<Concrete>;
#[cfg(any(feature = "std", test))]
pub type SystemConfig = system::GenesisConfig<Concrete>;
#[cfg(any(feature = "std", test))]
pub type SessionConfig = session::GenesisConfig<Concrete>;
#[cfg(any(feature = "std", test))]
pub type StakingConfig = staking::GenesisConfig<Concrete>;
#[cfg(any(feature = "std", test))]
pub type DemocracyConfig = democracy::GenesisConfig<Concrete>;
#[cfg(any(feature = "std", test))]
pub type CouncilConfig = council::GenesisConfig<Concrete>;
#[cfg(any(feature = "std", test))]
pub type ParachainsConfig = parachains::GenesisConfig<Concrete>;
#[cfg(any(feature = "std", test))]
pub struct GenesisConfig {
    pub consensus: Option<ConsensusConfig>,
    pub system: Option<SystemConfig>,
    pub session: Option<SessionConfig>,
    pub staking: Option<StakingConfig>,
    pub democracy: Option<DemocracyConfig>,
    pub council: Option<CouncilConfig>,
    pub parachains: Option<ParachainsConfig>,
}
#[cfg(any(feature = "std", test))]
impl ::BuildExternalities for GenesisConfig {
    fn build_externalities(self) -> ::BuiltExternalities {
        let mut s = ::BuiltExternalities::new();
        if let Some(extra) = self.consensus {
            s.extend(extra.build_externalities());
        }
        if let Some(extra) = self.system {
            s.extend(extra.build_externalities());
        }
        if let Some(extra) = self.session {
            s.extend(extra.build_externalities());
        }
        if let Some(extra) = self.staking {
            s.extend(extra.build_externalities());
        }
        if let Some(extra) = self.democracy {
            s.extend(extra.build_externalities());
        }
        if let Some(extra) = self.council {
            s.extend(extra.build_externalities());
        }
        if let Some(extra) = self.parachains {
            s.extend(extra.build_externalities());
        }
        s
    }
}
pub mod api {
    /// Dispatch logic for the native runtime.
    pub fn dispatch(method: &str, data: &[u8]) -> Option<Vec<u8>> {
        match method {
            "authorities" => {
                {
                    let mut data = data;
                    let input =
                        match ::codec::Slicable::decode(&mut data) {
                            Some(input) => input,
                            None => {
                                ::rt::begin_panic_fmt(&::std::fmt::Arguments::new_v1_formatted(&["Bad input data provided to "],
                                                                                               &match (&"authorities",)
                                                                                                    {
                                                                                                    (arg0,)
                                                                                                    =>
                                                                                                    [::std::fmt::ArgumentV1::new(arg0,
                                                                                                                                 ::std::fmt::Display::fmt)],
                                                                                                },
                                                                                               &[::std::fmt::rt::v1::Argument{position:
                                                                                                                                  ::std::fmt::rt::v1::Position::At(0usize),
                                                                                                                              format:
                                                                                                                                  ::std::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                                     ' ',
                                                                                                                                                                 align:
                                                                                                                                                                     ::std::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                                 flags:
                                                                                                                                                                     0u32,
                                                                                                                                                                 precision:
                                                                                                                                                                     ::std::fmt::rt::v1::Count::Implied,
                                                                                                                                                                 width:
                                                                                                                                                                     ::std::fmt::rt::v1::Count::Implied,},}]),
                                                      &("polkadot/runtime/src/lib.rs",
                                                        195u32, 2u32))
                            }
                        };
                    let output =
                        (|()| super::Consensus::authorities())(input);
                    Some(::codec::Slicable::encode(&output))
                }
            }
            "initialise_block" => {
                {
                    let mut data = data;
                    let input =
                        match ::codec::Slicable::decode(&mut data) {
                            Some(input) => input,
                            None => {
                                ::rt::begin_panic_fmt(&::std::fmt::Arguments::new_v1_formatted(&["Bad input data provided to "],
                                                                                               &match (&"initialise_block",)
                                                                                                    {
                                                                                                    (arg0,)
                                                                                                    =>
                                                                                                    [::std::fmt::ArgumentV1::new(arg0,
                                                                                                                                 ::std::fmt::Display::fmt)],
                                                                                                },
                                                                                               &[::std::fmt::rt::v1::Argument{position:
                                                                                                                                  ::std::fmt::rt::v1::Position::At(0usize),
                                                                                                                              format:
                                                                                                                                  ::std::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                                     ' ',
                                                                                                                                                                 align:
                                                                                                                                                                     ::std::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                                 flags:
                                                                                                                                                                     0u32,
                                                                                                                                                                 precision:
                                                                                                                                                                     ::std::fmt::rt::v1::Count::Implied,
                                                                                                                                                                 width:
                                                                                                                                                                     ::std::fmt::rt::v1::Count::Implied,},}]),
                                                      &("polkadot/runtime/src/lib.rs",
                                                        195u32, 2u32))
                            }
                        };
                    let output =
                        (|header|
                             super::Executive::initialise_block(&header))(input);
                    Some(::codec::Slicable::encode(&output))
                }
            }
            "apply_extrinsic" => {
                {
                    let mut data = data;
                    let input =
                        match ::codec::Slicable::decode(&mut data) {
                            Some(input) => input,
                            None => {
                                ::rt::begin_panic_fmt(&::std::fmt::Arguments::new_v1_formatted(&["Bad input data provided to "],
                                                                                               &match (&"apply_extrinsic",)
                                                                                                    {
                                                                                                    (arg0,)
                                                                                                    =>
                                                                                                    [::std::fmt::ArgumentV1::new(arg0,
                                                                                                                                 ::std::fmt::Display::fmt)],
                                                                                                },
                                                                                               &[::std::fmt::rt::v1::Argument{position:
                                                                                                                                  ::std::fmt::rt::v1::Position::At(0usize),
                                                                                                                              format:
                                                                                                                                  ::std::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                                     ' ',
                                                                                                                                                                 align:
                                                                                                                                                                     ::std::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                                 flags:
                                                                                                                                                                     0u32,
                                                                                                                                                                 precision:
                                                                                                                                                                     ::std::fmt::rt::v1::Count::Implied,
                                                                                                                                                                 width:
                                                                                                                                                                     ::std::fmt::rt::v1::Count::Implied,},}]),
                                                      &("polkadot/runtime/src/lib.rs",
                                                        195u32, 2u32))
                            }
                        };
                    let output =
                        (|extrinsic|
                             super::Executive::apply_extrinsic(extrinsic))(input);
                    Some(::codec::Slicable::encode(&output))
                }
            }
            "execute_block" => {
                {
                    let mut data = data;
                    let input =
                        match ::codec::Slicable::decode(&mut data) {
                            Some(input) => input,
                            None => {
                                ::rt::begin_panic_fmt(&::std::fmt::Arguments::new_v1_formatted(&["Bad input data provided to "],
                                                                                               &match (&"execute_block",)
                                                                                                    {
                                                                                                    (arg0,)
                                                                                                    =>
                                                                                                    [::std::fmt::ArgumentV1::new(arg0,
                                                                                                                                 ::std::fmt::Display::fmt)],
                                                                                                },
                                                                                               &[::std::fmt::rt::v1::Argument{position:
                                                                                                                                  ::std::fmt::rt::v1::Position::At(0usize),
                                                                                                                              format:
                                                                                                                                  ::std::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                                     ' ',
                                                                                                                                                                 align:
                                                                                                                                                                     ::std::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                                 flags:
                                                                                                                                                                     0u32,
                                                                                                                                                                 precision:
                                                                                                                                                                     ::std::fmt::rt::v1::Count::Implied,
                                                                                                                                                                 width:
                                                                                                                                                                     ::std::fmt::rt::v1::Count::Implied,},}]),
                                                      &("polkadot/runtime/src/lib.rs",
                                                        195u32, 2u32))
                            }
                        };
                    let output =
                        (|block|
                             super::Executive::execute_block(block))(input);
                    Some(::codec::Slicable::encode(&output))
                }
            }
            "finalise_block" => {
                {
                    let mut data = data;
                    let input =
                        match ::codec::Slicable::decode(&mut data) {
                            Some(input) => input,
                            None => {
                                ::rt::begin_panic_fmt(&::std::fmt::Arguments::new_v1_formatted(&["Bad input data provided to "],
                                                                                               &match (&"finalise_block",)
                                                                                                    {
                                                                                                    (arg0,)
                                                                                                    =>
                                                                                                    [::std::fmt::ArgumentV1::new(arg0,
                                                                                                                                 ::std::fmt::Display::fmt)],
                                                                                                },
                                                                                               &[::std::fmt::rt::v1::Argument{position:
                                                                                                                                  ::std::fmt::rt::v1::Position::At(0usize),
                                                                                                                              format:
                                                                                                                                  ::std::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                                     ' ',
                                                                                                                                                                 align:
                                                                                                                                                                     ::std::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                                 flags:
                                                                                                                                                                     0u32,
                                                                                                                                                                 precision:
                                                                                                                                                                     ::std::fmt::rt::v1::Count::Implied,
                                                                                                                                                                 width:
                                                                                                                                                                     ::std::fmt::rt::v1::Count::Implied,},}]),
                                                      &("polkadot/runtime/src/lib.rs",
                                                        195u32, 2u32))
                            }
                        };
                    let output =
                        (|()| super::Executive::finalise_block())(input);
                    Some(::codec::Slicable::encode(&output))
                }
            }
            "validator_count" => {
                {
                    let mut data = data;
                    let input =
                        match ::codec::Slicable::decode(&mut data) {
                            Some(input) => input,
                            None => {
                                ::rt::begin_panic_fmt(&::std::fmt::Arguments::new_v1_formatted(&["Bad input data provided to "],
                                                                                               &match (&"validator_count",)
                                                                                                    {
                                                                                                    (arg0,)
                                                                                                    =>
                                                                                                    [::std::fmt::ArgumentV1::new(arg0,
                                                                                                                                 ::std::fmt::Display::fmt)],
                                                                                                },
                                                                                               &[::std::fmt::rt::v1::Argument{position:
                                                                                                                                  ::std::fmt::rt::v1::Position::At(0usize),
                                                                                                                              format:
                                                                                                                                  ::std::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                                     ' ',
                                                                                                                                                                 align:
                                                                                                                                                                     ::std::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                                 flags:
                                                                                                                                                                     0u32,
                                                                                                                                                                 precision:
                                                                                                                                                                     ::std::fmt::rt::v1::Count::Implied,
                                                                                                                                                                 width:
                                                                                                                                                                     ::std::fmt::rt::v1::Count::Implied,},}]),
                                                      &("polkadot/runtime/src/lib.rs",
                                                        195u32, 2u32))
                            }
                        };
                    let output =
                        (|()| super::Session::validator_count())(input);
                    Some(::codec::Slicable::encode(&output))
                }
            }
            "validators" => {
                {
                    let mut data = data;
                    let input =
                        match ::codec::Slicable::decode(&mut data) {
                            Some(input) => input,
                            None => {
                                ::rt::begin_panic_fmt(&::std::fmt::Arguments::new_v1_formatted(&["Bad input data provided to "],
                                                                                               &match (&"validators",)
                                                                                                    {
                                                                                                    (arg0,)
                                                                                                    =>
                                                                                                    [::std::fmt::ArgumentV1::new(arg0,
                                                                                                                                 ::std::fmt::Display::fmt)],
                                                                                                },
                                                                                               &[::std::fmt::rt::v1::Argument{position:
                                                                                                                                  ::std::fmt::rt::v1::Position::At(0usize),
                                                                                                                              format:
                                                                                                                                  ::std::fmt::rt::v1::FormatSpec{fill:
                                                                                                                                                                     ' ',
                                                                                                                                                                 align:
                                                                                                                                                                     ::std::fmt::rt::v1::Alignment::Unknown,
                                                                                                                                                                 flags:
                                                                                                                                                                     0u32,
                                                                                                                                                                 precision:
                                                                                                                                                                     ::std::fmt::rt::v1::Count::Implied,
                                                                                                                                                                 width:
                                                                                                                                                                     ::std::fmt::rt::v1::Count::Implied,},}]),
                                                      &("polkadot/runtime/src/lib.rs",
                                                        195u32, 2u32))
                            }
                        };
                    let output = (|()| super::Session::validators())(input);
                    Some(::codec::Slicable::encode(&output))
                }
            }
            _ => None,
        }
    }
}
