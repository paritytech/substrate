pub struct Runtime;
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::core::clone::Clone for Runtime {
    #[inline]
    fn clone(&self) -> Runtime {
        {
            *self
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::core::marker::Copy for Runtime {}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::core::cmp::PartialEq for Runtime {
    #[inline]
    fn eq(&self, other: &Runtime) -> bool {
        match *other {
            Runtime => match *self {
                Runtime => true,
            },
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::core::cmp::Eq for Runtime {
    #[inline]
    #[doc(hidden)]
    fn assert_receiver_is_total_eq(&self) -> () {
        {}
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::core::fmt::Debug for Runtime {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        match *self {
            Runtime => {
                let mut debug_trait_builder = f.debug_tuple("Runtime");
                debug_trait_builder.finish()
            }
        }
    }
}
impl ::srml_support::sr_primitives::traits::GetNodeBlockType for Runtime {
    type NodeBlock = node_primitives::Block;
}
impl ::srml_support::sr_primitives::traits::GetRuntimeBlockType for Runtime {
    type RuntimeBlock = Block;
}
#[allow(non_camel_case_types)]
pub enum Event {
    system(system::Event),
    indices(indices::Event<Runtime>),
    balances(balances::Event<Runtime>),
    staking(staking::Event<Runtime>),
    session(session::Event),
    democracy(democracy::Event<Runtime>),
    collective_Instance1(collective::Event<Runtime, collective::Instance1>),
    collective_Instance2(collective::Event<Runtime, collective::Instance2>),
    elections(elections::Event<Runtime>),
    membership_Instance1(membership::Event<Runtime, membership::Instance1>),
    grandpa(grandpa::Event),
    treasury(treasury::Event<Runtime>),
    contracts(contracts::Event<Runtime>),
    sudo(sudo::Event<Runtime>),
    im_online(im_online::Event<Runtime>),
    offences(offences::Event),
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl ::core::clone::Clone for Event {
    #[inline]
    fn clone(&self) -> Event {
        match (&*self,) {
            (&Event::system(ref __self_0),) => {
                Event::system(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Event::indices(ref __self_0),) => {
                Event::indices(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Event::balances(ref __self_0),) => {
                Event::balances(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Event::staking(ref __self_0),) => {
                Event::staking(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Event::session(ref __self_0),) => {
                Event::session(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Event::democracy(ref __self_0),) => {
                Event::democracy(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Event::collective_Instance1(ref __self_0),) => {
                Event::collective_Instance1(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Event::collective_Instance2(ref __self_0),) => {
                Event::collective_Instance2(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Event::elections(ref __self_0),) => {
                Event::elections(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Event::membership_Instance1(ref __self_0),) => {
                Event::membership_Instance1(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Event::grandpa(ref __self_0),) => {
                Event::grandpa(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Event::treasury(ref __self_0),) => {
                Event::treasury(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Event::contracts(ref __self_0),) => {
                Event::contracts(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Event::sudo(ref __self_0),) => Event::sudo(::core::clone::Clone::clone(&(*__self_0))),
            (&Event::im_online(ref __self_0),) => {
                Event::im_online(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Event::offences(ref __self_0),) => {
                Event::offences(::core::clone::Clone::clone(&(*__self_0)))
            }
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl ::core::cmp::PartialEq for Event {
    #[inline]
    fn eq(&self, other: &Event) -> bool {
        {
            let __self_vi = unsafe { ::core::intrinsics::discriminant_value(&*self) } as isize;
            let __arg_1_vi = unsafe { ::core::intrinsics::discriminant_value(&*other) } as isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&Event::system(ref __self_0), &Event::system(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Event::indices(ref __self_0), &Event::indices(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Event::balances(ref __self_0), &Event::balances(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Event::staking(ref __self_0), &Event::staking(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Event::session(ref __self_0), &Event::session(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Event::democracy(ref __self_0), &Event::democracy(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (
                        &Event::collective_Instance1(ref __self_0),
                        &Event::collective_Instance1(ref __arg_1_0),
                    ) => (*__self_0) == (*__arg_1_0),
                    (
                        &Event::collective_Instance2(ref __self_0),
                        &Event::collective_Instance2(ref __arg_1_0),
                    ) => (*__self_0) == (*__arg_1_0),
                    (&Event::elections(ref __self_0), &Event::elections(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (
                        &Event::membership_Instance1(ref __self_0),
                        &Event::membership_Instance1(ref __arg_1_0),
                    ) => (*__self_0) == (*__arg_1_0),
                    (&Event::grandpa(ref __self_0), &Event::grandpa(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Event::treasury(ref __self_0), &Event::treasury(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Event::contracts(ref __self_0), &Event::contracts(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Event::sudo(ref __self_0), &Event::sudo(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Event::im_online(ref __self_0), &Event::im_online(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Event::offences(ref __self_0), &Event::offences(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    _ => unsafe { ::core::intrinsics::unreachable() },
                }
            } else {
                false
            }
        }
    }
    #[inline]
    fn ne(&self, other: &Event) -> bool {
        {
            let __self_vi = unsafe { ::core::intrinsics::discriminant_value(&*self) } as isize;
            let __arg_1_vi = unsafe { ::core::intrinsics::discriminant_value(&*other) } as isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&Event::system(ref __self_0), &Event::system(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Event::indices(ref __self_0), &Event::indices(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Event::balances(ref __self_0), &Event::balances(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Event::staking(ref __self_0), &Event::staking(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Event::session(ref __self_0), &Event::session(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Event::democracy(ref __self_0), &Event::democracy(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (
                        &Event::collective_Instance1(ref __self_0),
                        &Event::collective_Instance1(ref __arg_1_0),
                    ) => (*__self_0) != (*__arg_1_0),
                    (
                        &Event::collective_Instance2(ref __self_0),
                        &Event::collective_Instance2(ref __arg_1_0),
                    ) => (*__self_0) != (*__arg_1_0),
                    (&Event::elections(ref __self_0), &Event::elections(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (
                        &Event::membership_Instance1(ref __self_0),
                        &Event::membership_Instance1(ref __arg_1_0),
                    ) => (*__self_0) != (*__arg_1_0),
                    (&Event::grandpa(ref __self_0), &Event::grandpa(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Event::treasury(ref __self_0), &Event::treasury(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Event::contracts(ref __self_0), &Event::contracts(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Event::sudo(ref __self_0), &Event::sudo(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Event::im_online(ref __self_0), &Event::im_online(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Event::offences(ref __self_0), &Event::offences(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    _ => unsafe { ::core::intrinsics::unreachable() },
                }
            } else {
                true
            }
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl ::core::cmp::Eq for Event {
    #[inline]
    #[doc(hidden)]
    fn assert_receiver_is_total_eq(&self) -> () {
        {
            let _: ::core::cmp::AssertParamIsEq<system::Event>;
            let _: ::core::cmp::AssertParamIsEq<indices::Event<Runtime>>;
            let _: ::core::cmp::AssertParamIsEq<balances::Event<Runtime>>;
            let _: ::core::cmp::AssertParamIsEq<staking::Event<Runtime>>;
            let _: ::core::cmp::AssertParamIsEq<session::Event>;
            let _: ::core::cmp::AssertParamIsEq<democracy::Event<Runtime>>;
            let _: ::core::cmp::AssertParamIsEq<collective::Event<Runtime, collective::Instance1>>;
            let _: ::core::cmp::AssertParamIsEq<collective::Event<Runtime, collective::Instance2>>;
            let _: ::core::cmp::AssertParamIsEq<elections::Event<Runtime>>;
            let _: ::core::cmp::AssertParamIsEq<membership::Event<Runtime, membership::Instance1>>;
            let _: ::core::cmp::AssertParamIsEq<grandpa::Event>;
            let _: ::core::cmp::AssertParamIsEq<treasury::Event<Runtime>>;
            let _: ::core::cmp::AssertParamIsEq<contracts::Event<Runtime>>;
            let _: ::core::cmp::AssertParamIsEq<sudo::Event<Runtime>>;
            let _: ::core::cmp::AssertParamIsEq<im_online::Event<Runtime>>;
            let _: ::core::cmp::AssertParamIsEq<offences::Event>;
        }
    }
}
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_ENCODE_FOR_Event: () = {
    #[allow(unknown_lints)]
    #[allow(rust_2018_idioms)]
    extern crate codec as _parity_scale_codec;
    impl _parity_scale_codec::Encode for Event {
        fn encode_to<EncOut: _parity_scale_codec::Output>(&self, dest: &mut EncOut) {
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
                Event::staking(ref aa) => {
                    dest.push_byte(3usize as u8);
                    dest.push(aa);
                }
                Event::session(ref aa) => {
                    dest.push_byte(4usize as u8);
                    dest.push(aa);
                }
                Event::democracy(ref aa) => {
                    dest.push_byte(5usize as u8);
                    dest.push(aa);
                }
                Event::collective_Instance1(ref aa) => {
                    dest.push_byte(6usize as u8);
                    dest.push(aa);
                }
                Event::collective_Instance2(ref aa) => {
                    dest.push_byte(7usize as u8);
                    dest.push(aa);
                }
                Event::elections(ref aa) => {
                    dest.push_byte(8usize as u8);
                    dest.push(aa);
                }
                Event::membership_Instance1(ref aa) => {
                    dest.push_byte(9usize as u8);
                    dest.push(aa);
                }
                Event::grandpa(ref aa) => {
                    dest.push_byte(10usize as u8);
                    dest.push(aa);
                }
                Event::treasury(ref aa) => {
                    dest.push_byte(11usize as u8);
                    dest.push(aa);
                }
                Event::contracts(ref aa) => {
                    dest.push_byte(12usize as u8);
                    dest.push(aa);
                }
                Event::sudo(ref aa) => {
                    dest.push_byte(13usize as u8);
                    dest.push(aa);
                }
                Event::im_online(ref aa) => {
                    dest.push_byte(14usize as u8);
                    dest.push(aa);
                }
                Event::offences(ref aa) => {
                    dest.push_byte(15usize as u8);
                    dest.push(aa);
                }
                _ => (),
            }
        }
    }
    impl _parity_scale_codec::EncodeLike for Event {}
};
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_DECODE_FOR_Event: () = {
    #[allow(unknown_lints)]
    #[allow(rust_2018_idioms)]
    extern crate codec as _parity_scale_codec;
    impl _parity_scale_codec::Decode for Event {
        fn decode<DecIn: _parity_scale_codec::Input>(
            input: &mut DecIn,
        ) -> core::result::Result<Self, _parity_scale_codec::Error> {
            match input.read_byte()? {
                x if x == 0usize as u8 => Ok(Event::system({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Event :: system.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 1usize as u8 => Ok(Event::indices({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Event :: indices.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 2usize as u8 => Ok(Event::balances({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Event :: balances.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 3usize as u8 => Ok(Event::staking({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Event :: staking.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 4usize as u8 => Ok(Event::session({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Event :: session.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 5usize as u8 => Ok(Event::democracy({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Event :: democracy.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 6usize as u8 => Ok(Event::collective_Instance1({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => {
                            return Err(
                                "Error decoding field Event :: collective_Instance1.0".into()
                            )
                        }
                        Ok(a) => a,
                    }
                })),
                x if x == 7usize as u8 => Ok(Event::collective_Instance2({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => {
                            return Err(
                                "Error decoding field Event :: collective_Instance2.0".into()
                            )
                        }
                        Ok(a) => a,
                    }
                })),
                x if x == 8usize as u8 => Ok(Event::elections({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Event :: elections.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 9usize as u8 => Ok(Event::membership_Instance1({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => {
                            return Err(
                                "Error decoding field Event :: membership_Instance1.0".into()
                            )
                        }
                        Ok(a) => a,
                    }
                })),
                x if x == 10usize as u8 => Ok(Event::grandpa({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Event :: grandpa.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 11usize as u8 => Ok(Event::treasury({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Event :: treasury.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 12usize as u8 => Ok(Event::contracts({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Event :: contracts.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 13usize as u8 => Ok(Event::sudo({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Event :: sudo.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 14usize as u8 => Ok(Event::im_online({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Event :: im_online.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 15usize as u8 => Ok(Event::offences({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Event :: offences.0".into()),
                        Ok(a) => a,
                    }
                })),
                x => Err("No such variant in enum Event".into()),
            }
        }
    }
};
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl ::core::fmt::Debug for Event {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
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
            (&Event::staking(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("staking");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::session(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("session");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::democracy(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("democracy");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::collective_Instance1(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("collective_Instance1");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::collective_Instance2(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("collective_Instance2");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::elections(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("elections");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::membership_Instance1(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("membership_Instance1");
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
            (&Event::contracts(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("contracts");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::sudo(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("sudo");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::im_online(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("im_online");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Event::offences(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("offences");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
        }
    }
}
impl From<system::Event> for Event {
    fn from(x: system::Event) -> Self {
        Event::system(x)
    }
}
impl From<indices::Event<Runtime>> for Event {
    fn from(x: indices::Event<Runtime>) -> Self {
        Event::indices(x)
    }
}
impl ::srml_support::rstd::convert::TryInto<indices::Event<Runtime>> for Event {
    type Error = ();
    fn try_into(
        self,
    ) -> ::srml_support::rstd::result::Result<indices::Event<Runtime>, Self::Error> {
        match self {
            Self::indices(evt) => Ok(evt),
            _ => Err(()),
        }
    }
}
impl From<balances::Event<Runtime>> for Event {
    fn from(x: balances::Event<Runtime>) -> Self {
        Event::balances(x)
    }
}
impl ::srml_support::rstd::convert::TryInto<balances::Event<Runtime>> for Event {
    type Error = ();
    fn try_into(
        self,
    ) -> ::srml_support::rstd::result::Result<balances::Event<Runtime>, Self::Error> {
        match self {
            Self::balances(evt) => Ok(evt),
            _ => Err(()),
        }
    }
}
impl From<staking::Event<Runtime>> for Event {
    fn from(x: staking::Event<Runtime>) -> Self {
        Event::staking(x)
    }
}
impl ::srml_support::rstd::convert::TryInto<staking::Event<Runtime>> for Event {
    type Error = ();
    fn try_into(
        self,
    ) -> ::srml_support::rstd::result::Result<staking::Event<Runtime>, Self::Error> {
        match self {
            Self::staking(evt) => Ok(evt),
            _ => Err(()),
        }
    }
}
impl From<session::Event> for Event {
    fn from(x: session::Event) -> Self {
        Event::session(x)
    }
}
impl ::srml_support::rstd::convert::TryInto<session::Event> for Event {
    type Error = ();
    fn try_into(self) -> ::srml_support::rstd::result::Result<session::Event, Self::Error> {
        match self {
            Self::session(evt) => Ok(evt),
            _ => Err(()),
        }
    }
}
impl From<democracy::Event<Runtime>> for Event {
    fn from(x: democracy::Event<Runtime>) -> Self {
        Event::democracy(x)
    }
}
impl ::srml_support::rstd::convert::TryInto<democracy::Event<Runtime>> for Event {
    type Error = ();
    fn try_into(
        self,
    ) -> ::srml_support::rstd::result::Result<democracy::Event<Runtime>, Self::Error> {
        match self {
            Self::democracy(evt) => Ok(evt),
            _ => Err(()),
        }
    }
}
impl From<collective::Event<Runtime, collective::Instance1>> for Event {
    fn from(x: collective::Event<Runtime, collective::Instance1>) -> Self {
        Event::collective_Instance1(x)
    }
}
impl ::srml_support::rstd::convert::TryInto<collective::Event<Runtime, collective::Instance1>>
    for Event
{
    type Error = ();
    fn try_into(
        self,
    ) -> ::srml_support::rstd::result::Result<
        collective::Event<Runtime, collective::Instance1>,
        Self::Error,
    > {
        match self {
            Self::collective_Instance1(evt) => Ok(evt),
            _ => Err(()),
        }
    }
}
impl From<collective::Event<Runtime, collective::Instance2>> for Event {
    fn from(x: collective::Event<Runtime, collective::Instance2>) -> Self {
        Event::collective_Instance2(x)
    }
}
impl ::srml_support::rstd::convert::TryInto<collective::Event<Runtime, collective::Instance2>>
    for Event
{
    type Error = ();
    fn try_into(
        self,
    ) -> ::srml_support::rstd::result::Result<
        collective::Event<Runtime, collective::Instance2>,
        Self::Error,
    > {
        match self {
            Self::collective_Instance2(evt) => Ok(evt),
            _ => Err(()),
        }
    }
}
impl From<elections::Event<Runtime>> for Event {
    fn from(x: elections::Event<Runtime>) -> Self {
        Event::elections(x)
    }
}
impl ::srml_support::rstd::convert::TryInto<elections::Event<Runtime>> for Event {
    type Error = ();
    fn try_into(
        self,
    ) -> ::srml_support::rstd::result::Result<elections::Event<Runtime>, Self::Error> {
        match self {
            Self::elections(evt) => Ok(evt),
            _ => Err(()),
        }
    }
}
impl From<membership::Event<Runtime, membership::Instance1>> for Event {
    fn from(x: membership::Event<Runtime, membership::Instance1>) -> Self {
        Event::membership_Instance1(x)
    }
}
impl ::srml_support::rstd::convert::TryInto<membership::Event<Runtime, membership::Instance1>>
    for Event
{
    type Error = ();
    fn try_into(
        self,
    ) -> ::srml_support::rstd::result::Result<
        membership::Event<Runtime, membership::Instance1>,
        Self::Error,
    > {
        match self {
            Self::membership_Instance1(evt) => Ok(evt),
            _ => Err(()),
        }
    }
}
impl From<grandpa::Event> for Event {
    fn from(x: grandpa::Event) -> Self {
        Event::grandpa(x)
    }
}
impl ::srml_support::rstd::convert::TryInto<grandpa::Event> for Event {
    type Error = ();
    fn try_into(self) -> ::srml_support::rstd::result::Result<grandpa::Event, Self::Error> {
        match self {
            Self::grandpa(evt) => Ok(evt),
            _ => Err(()),
        }
    }
}
impl From<treasury::Event<Runtime>> for Event {
    fn from(x: treasury::Event<Runtime>) -> Self {
        Event::treasury(x)
    }
}
impl ::srml_support::rstd::convert::TryInto<treasury::Event<Runtime>> for Event {
    type Error = ();
    fn try_into(
        self,
    ) -> ::srml_support::rstd::result::Result<treasury::Event<Runtime>, Self::Error> {
        match self {
            Self::treasury(evt) => Ok(evt),
            _ => Err(()),
        }
    }
}
impl From<contracts::Event<Runtime>> for Event {
    fn from(x: contracts::Event<Runtime>) -> Self {
        Event::contracts(x)
    }
}
impl ::srml_support::rstd::convert::TryInto<contracts::Event<Runtime>> for Event {
    type Error = ();
    fn try_into(
        self,
    ) -> ::srml_support::rstd::result::Result<contracts::Event<Runtime>, Self::Error> {
        match self {
            Self::contracts(evt) => Ok(evt),
            _ => Err(()),
        }
    }
}
impl From<sudo::Event<Runtime>> for Event {
    fn from(x: sudo::Event<Runtime>) -> Self {
        Event::sudo(x)
    }
}
impl ::srml_support::rstd::convert::TryInto<sudo::Event<Runtime>> for Event {
    type Error = ();
    fn try_into(self) -> ::srml_support::rstd::result::Result<sudo::Event<Runtime>, Self::Error> {
        match self {
            Self::sudo(evt) => Ok(evt),
            _ => Err(()),
        }
    }
}
impl From<im_online::Event<Runtime>> for Event {
    fn from(x: im_online::Event<Runtime>) -> Self {
        Event::im_online(x)
    }
}
impl ::srml_support::rstd::convert::TryInto<im_online::Event<Runtime>> for Event {
    type Error = ();
    fn try_into(
        self,
    ) -> ::srml_support::rstd::result::Result<im_online::Event<Runtime>, Self::Error> {
        match self {
            Self::im_online(evt) => Ok(evt),
            _ => Err(()),
        }
    }
}
impl From<offences::Event> for Event {
    fn from(x: offences::Event) -> Self {
        Event::offences(x)
    }
}
impl ::srml_support::rstd::convert::TryInto<offences::Event> for Event {
    type Error = ();
    fn try_into(self) -> ::srml_support::rstd::result::Result<offences::Event, Self::Error> {
        match self {
            Self::offences(evt) => Ok(evt),
            _ => Err(()),
        }
    }
}
impl Runtime {
    #[allow(dead_code)]
    pub fn outer_event_metadata() -> ::srml_support::event::OuterEventMetadata {
        ::srml_support::event::OuterEventMetadata {
            name: ::srml_support::event::DecodeDifferent::Encode("Event"),
            events: ::srml_support::event::DecodeDifferent::Encode(&[
                (
                    "system",
                    ::srml_support::event::FnEncode(system::Event::metadata),
                ),
                (
                    "indices",
                    ::srml_support::event::FnEncode(indices::Event::<Runtime>::metadata),
                ),
                (
                    "balances",
                    ::srml_support::event::FnEncode(balances::Event::<Runtime>::metadata),
                ),
                (
                    "staking",
                    ::srml_support::event::FnEncode(staking::Event::<Runtime>::metadata),
                ),
                (
                    "session",
                    ::srml_support::event::FnEncode(session::Event::metadata),
                ),
                (
                    "democracy",
                    ::srml_support::event::FnEncode(democracy::Event::<Runtime>::metadata),
                ),
                (
                    "collective",
                    ::srml_support::event::FnEncode(
                        collective::Event::<Runtime, collective::Instance1>::metadata,
                    ),
                ),
                (
                    "collective",
                    ::srml_support::event::FnEncode(
                        collective::Event::<Runtime, collective::Instance2>::metadata,
                    ),
                ),
                (
                    "elections",
                    ::srml_support::event::FnEncode(elections::Event::<Runtime>::metadata),
                ),
                (
                    "membership",
                    ::srml_support::event::FnEncode(
                        membership::Event::<Runtime, membership::Instance1>::metadata,
                    ),
                ),
                (
                    "grandpa",
                    ::srml_support::event::FnEncode(grandpa::Event::metadata),
                ),
                (
                    "treasury",
                    ::srml_support::event::FnEncode(treasury::Event::<Runtime>::metadata),
                ),
                (
                    "contracts",
                    ::srml_support::event::FnEncode(contracts::Event::<Runtime>::metadata),
                ),
                (
                    "sudo",
                    ::srml_support::event::FnEncode(sudo::Event::<Runtime>::metadata),
                ),
                (
                    "im_online",
                    ::srml_support::event::FnEncode(im_online::Event::<Runtime>::metadata),
                ),
                (
                    "offences",
                    ::srml_support::event::FnEncode(offences::Event::metadata),
                ),
            ]),
        }
    }
    #[allow(dead_code)]
    pub fn __module_events_system() -> &'static [::srml_support::event::EventMetadata] {
        system::Event::metadata()
    }
    #[allow(dead_code)]
    pub fn __module_events_indices() -> &'static [::srml_support::event::EventMetadata] {
        indices::Event::<Runtime>::metadata()
    }
    #[allow(dead_code)]
    pub fn __module_events_balances() -> &'static [::srml_support::event::EventMetadata] {
        balances::Event::<Runtime>::metadata()
    }
    #[allow(dead_code)]
    pub fn __module_events_staking() -> &'static [::srml_support::event::EventMetadata] {
        staking::Event::<Runtime>::metadata()
    }
    #[allow(dead_code)]
    pub fn __module_events_session() -> &'static [::srml_support::event::EventMetadata] {
        session::Event::metadata()
    }
    #[allow(dead_code)]
    pub fn __module_events_democracy() -> &'static [::srml_support::event::EventMetadata] {
        democracy::Event::<Runtime>::metadata()
    }
    #[allow(dead_code)]
    pub fn __module_events_collective_Instance1() -> &'static [::srml_support::event::EventMetadata]
    {
        collective::Event::<Runtime, collective::Instance1>::metadata()
    }
    #[allow(dead_code)]
    pub fn __module_events_collective_Instance2() -> &'static [::srml_support::event::EventMetadata]
    {
        collective::Event::<Runtime, collective::Instance2>::metadata()
    }
    #[allow(dead_code)]
    pub fn __module_events_elections() -> &'static [::srml_support::event::EventMetadata] {
        elections::Event::<Runtime>::metadata()
    }
    #[allow(dead_code)]
    pub fn __module_events_membership_Instance1() -> &'static [::srml_support::event::EventMetadata]
    {
        membership::Event::<Runtime, membership::Instance1>::metadata()
    }
    #[allow(dead_code)]
    pub fn __module_events_grandpa() -> &'static [::srml_support::event::EventMetadata] {
        grandpa::Event::metadata()
    }
    #[allow(dead_code)]
    pub fn __module_events_treasury() -> &'static [::srml_support::event::EventMetadata] {
        treasury::Event::<Runtime>::metadata()
    }
    #[allow(dead_code)]
    pub fn __module_events_contracts() -> &'static [::srml_support::event::EventMetadata] {
        contracts::Event::<Runtime>::metadata()
    }
    #[allow(dead_code)]
    pub fn __module_events_sudo() -> &'static [::srml_support::event::EventMetadata] {
        sudo::Event::<Runtime>::metadata()
    }
    #[allow(dead_code)]
    pub fn __module_events_im_online() -> &'static [::srml_support::event::EventMetadata] {
        im_online::Event::<Runtime>::metadata()
    }
    #[allow(dead_code)]
    pub fn __module_events_offences() -> &'static [::srml_support::event::EventMetadata] {
        offences::Event::metadata()
    }
}
#[allow(non_camel_case_types)]
pub enum Origin {
    system(system::Origin<Runtime>),
    collective_Instance1(collective::Origin<Runtime, collective::Instance1>),
    collective_Instance2(collective::Origin<Runtime, collective::Instance2>),
    #[allow(dead_code)]
    Void(::srml_support::Void),
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl ::core::clone::Clone for Origin {
    #[inline]
    fn clone(&self) -> Origin {
        match (&*self,) {
            (&Origin::system(ref __self_0),) => {
                Origin::system(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Origin::collective_Instance1(ref __self_0),) => {
                Origin::collective_Instance1(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Origin::collective_Instance2(ref __self_0),) => {
                Origin::collective_Instance2(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Origin::Void(ref __self_0),) => {
                Origin::Void(::core::clone::Clone::clone(&(*__self_0)))
            }
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl ::core::cmp::PartialEq for Origin {
    #[inline]
    fn eq(&self, other: &Origin) -> bool {
        {
            let __self_vi = unsafe { ::core::intrinsics::discriminant_value(&*self) } as isize;
            let __arg_1_vi = unsafe { ::core::intrinsics::discriminant_value(&*other) } as isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&Origin::system(ref __self_0), &Origin::system(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (
                        &Origin::collective_Instance1(ref __self_0),
                        &Origin::collective_Instance1(ref __arg_1_0),
                    ) => (*__self_0) == (*__arg_1_0),
                    (
                        &Origin::collective_Instance2(ref __self_0),
                        &Origin::collective_Instance2(ref __arg_1_0),
                    ) => (*__self_0) == (*__arg_1_0),
                    (&Origin::Void(ref __self_0), &Origin::Void(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    _ => unsafe { ::core::intrinsics::unreachable() },
                }
            } else {
                false
            }
        }
    }
    #[inline]
    fn ne(&self, other: &Origin) -> bool {
        {
            let __self_vi = unsafe { ::core::intrinsics::discriminant_value(&*self) } as isize;
            let __arg_1_vi = unsafe { ::core::intrinsics::discriminant_value(&*other) } as isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&Origin::system(ref __self_0), &Origin::system(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (
                        &Origin::collective_Instance1(ref __self_0),
                        &Origin::collective_Instance1(ref __arg_1_0),
                    ) => (*__self_0) != (*__arg_1_0),
                    (
                        &Origin::collective_Instance2(ref __self_0),
                        &Origin::collective_Instance2(ref __arg_1_0),
                    ) => (*__self_0) != (*__arg_1_0),
                    (&Origin::Void(ref __self_0), &Origin::Void(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    _ => unsafe { ::core::intrinsics::unreachable() },
                }
            } else {
                true
            }
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl ::core::cmp::Eq for Origin {
    #[inline]
    #[doc(hidden)]
    fn assert_receiver_is_total_eq(&self) -> () {
        {
            let _: ::core::cmp::AssertParamIsEq<system::Origin<Runtime>>;
            let _: ::core::cmp::AssertParamIsEq<
                collective::Origin<Runtime, collective::Instance1>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                collective::Origin<Runtime, collective::Instance2>,
            >;
            let _: ::core::cmp::AssertParamIsEq<::srml_support::Void>;
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
#[allow(non_camel_case_types)]
impl ::core::fmt::Debug for Origin {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        match (&*self,) {
            (&Origin::system(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("system");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Origin::collective_Instance1(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("collective_Instance1");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Origin::collective_Instance2(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("collective_Instance2");
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
    pub const NONE: Self = Origin::system(system::RawOrigin::None);
    pub const ROOT: Self = Origin::system(system::RawOrigin::Root);
    pub fn signed(by: <Runtime as system::Trait>::AccountId) -> Self {
        Origin::system(system::RawOrigin::Signed(by))
    }
}
impl From<system::Origin<Runtime>> for Origin {
    fn from(x: system::Origin<Runtime>) -> Self {
        Origin::system(x)
    }
}
impl Into<::srml_support::rstd::result::Result<system::Origin<Runtime>, Origin>> for Origin {
    fn into(self) -> ::srml_support::rstd::result::Result<system::Origin<Runtime>, Self> {
        if let Origin::system(l) = self {
            Ok(l)
        } else {
            Err(self)
        }
    }
}
impl From<Option<<Runtime as system::Trait>::AccountId>> for Origin {
    fn from(x: Option<<Runtime as system::Trait>::AccountId>) -> Self {
        <system::Origin<Runtime>>::from(x).into()
    }
}
impl From<collective::Origin<Runtime, collective::Instance1>> for Origin {
    fn from(x: collective::Origin<Runtime, collective::Instance1>) -> Self {
        Origin::collective_Instance1(x)
    }
}
impl
    Into<
        ::srml_support::rstd::result::Result<
            collective::Origin<Runtime, collective::Instance1>,
            Origin,
        >,
    > for Origin
{
    fn into(
        self,
    ) -> ::srml_support::rstd::result::Result<
        collective::Origin<Runtime, collective::Instance1>,
        Self,
    > {
        if let Origin::collective_Instance1(l) = self {
            Ok(l)
        } else {
            Err(self)
        }
    }
}
impl From<collective::Origin<Runtime, collective::Instance2>> for Origin {
    fn from(x: collective::Origin<Runtime, collective::Instance2>) -> Self {
        Origin::collective_Instance2(x)
    }
}
impl
    Into<
        ::srml_support::rstd::result::Result<
            collective::Origin<Runtime, collective::Instance2>,
            Origin,
        >,
    > for Origin
{
    fn into(
        self,
    ) -> ::srml_support::rstd::result::Result<
        collective::Origin<Runtime, collective::Instance2>,
        Self,
    > {
        if let Origin::collective_Instance2(l) = self {
            Ok(l)
        } else {
            Err(self)
        }
    }
}
pub type System = system::Module<Runtime>;
pub type Babe = babe::Module<Runtime>;
pub type Timestamp = timestamp::Module<Runtime>;
pub type Authorship = authorship::Module<Runtime>;
pub type Indices = indices::Module<Runtime>;
pub type Balances = balances::Module<Runtime>;
pub type Staking = staking::Module<Runtime>;
pub type Session = session::Module<Runtime>;
pub type Democracy = democracy::Module<Runtime>;
pub type Council = collective::Module<Runtime, collective::Instance1>;
pub type TechnicalCommittee = collective::Module<Runtime, collective::Instance2>;
pub type Elections = elections::Module<Runtime>;
pub type TechnicalMembership = membership::Module<Runtime, membership::Instance1>;
pub type FinalityTracker = finality_tracker::Module<Runtime>;
pub type Grandpa = grandpa::Module<Runtime>;
pub type Treasury = treasury::Module<Runtime>;
pub type Contracts = contracts::Module<Runtime>;
pub type Sudo = sudo::Module<Runtime>;
pub type ImOnline = im_online::Module<Runtime>;
pub type AuthorityDiscovery = authority_discovery::Module<Runtime>;
pub type Offences = offences::Module<Runtime>;
pub type Bridge = bridge::Module<Runtime>;
type AllModules = (
    Babe,
    Timestamp,
    Authorship,
    Indices,
    Balances,
    Staking,
    Session,
    Democracy,
    Council,
    TechnicalCommittee,
    Elections,
    TechnicalMembership,
    FinalityTracker,
    Grandpa,
    Treasury,
    Contracts,
    Sudo,
    ImOnline,
    AuthorityDiscovery,
    Offences,
    Bridge,
);
pub enum Call {
    System(::srml_support::dispatch::CallableCallFor<System, Runtime>),
    Babe(::srml_support::dispatch::CallableCallFor<Babe, Runtime>),
    Timestamp(::srml_support::dispatch::CallableCallFor<Timestamp, Runtime>),
    Authorship(::srml_support::dispatch::CallableCallFor<Authorship, Runtime>),
    Indices(::srml_support::dispatch::CallableCallFor<Indices, Runtime>),
    Balances(::srml_support::dispatch::CallableCallFor<Balances, Runtime>),
    Staking(::srml_support::dispatch::CallableCallFor<Staking, Runtime>),
    Session(::srml_support::dispatch::CallableCallFor<Session, Runtime>),
    Democracy(::srml_support::dispatch::CallableCallFor<Democracy, Runtime>),
    Council(::srml_support::dispatch::CallableCallFor<Council, Runtime>),
    TechnicalCommittee(::srml_support::dispatch::CallableCallFor<TechnicalCommittee, Runtime>),
    Elections(::srml_support::dispatch::CallableCallFor<Elections, Runtime>),
    TechnicalMembership(::srml_support::dispatch::CallableCallFor<TechnicalMembership, Runtime>),
    FinalityTracker(::srml_support::dispatch::CallableCallFor<FinalityTracker, Runtime>),
    Grandpa(::srml_support::dispatch::CallableCallFor<Grandpa, Runtime>),
    Treasury(::srml_support::dispatch::CallableCallFor<Treasury, Runtime>),
    Contracts(::srml_support::dispatch::CallableCallFor<Contracts, Runtime>),
    Sudo(::srml_support::dispatch::CallableCallFor<Sudo, Runtime>),
    ImOnline(::srml_support::dispatch::CallableCallFor<ImOnline, Runtime>),
    AuthorityDiscovery(::srml_support::dispatch::CallableCallFor<AuthorityDiscovery, Runtime>),
    Offences(::srml_support::dispatch::CallableCallFor<Offences, Runtime>),
    Bridge(::srml_support::dispatch::CallableCallFor<Bridge, Runtime>),
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::core::clone::Clone for Call {
    #[inline]
    fn clone(&self) -> Call {
        match (&*self,) {
            (&Call::System(ref __self_0),) => {
                Call::System(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::Babe(ref __self_0),) => Call::Babe(::core::clone::Clone::clone(&(*__self_0))),
            (&Call::Timestamp(ref __self_0),) => {
                Call::Timestamp(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::Authorship(ref __self_0),) => {
                Call::Authorship(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::Indices(ref __self_0),) => {
                Call::Indices(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::Balances(ref __self_0),) => {
                Call::Balances(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::Staking(ref __self_0),) => {
                Call::Staking(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::Session(ref __self_0),) => {
                Call::Session(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::Democracy(ref __self_0),) => {
                Call::Democracy(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::Council(ref __self_0),) => {
                Call::Council(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::TechnicalCommittee(ref __self_0),) => {
                Call::TechnicalCommittee(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::Elections(ref __self_0),) => {
                Call::Elections(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::TechnicalMembership(ref __self_0),) => {
                Call::TechnicalMembership(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::FinalityTracker(ref __self_0),) => {
                Call::FinalityTracker(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::Grandpa(ref __self_0),) => {
                Call::Grandpa(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::Treasury(ref __self_0),) => {
                Call::Treasury(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::Contracts(ref __self_0),) => {
                Call::Contracts(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::Sudo(ref __self_0),) => Call::Sudo(::core::clone::Clone::clone(&(*__self_0))),
            (&Call::ImOnline(ref __self_0),) => {
                Call::ImOnline(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::AuthorityDiscovery(ref __self_0),) => {
                Call::AuthorityDiscovery(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::Offences(ref __self_0),) => {
                Call::Offences(::core::clone::Clone::clone(&(*__self_0)))
            }
            (&Call::Bridge(ref __self_0),) => {
                Call::Bridge(::core::clone::Clone::clone(&(*__self_0)))
            }
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::core::cmp::PartialEq for Call {
    #[inline]
    fn eq(&self, other: &Call) -> bool {
        {
            let __self_vi = unsafe { ::core::intrinsics::discriminant_value(&*self) } as isize;
            let __arg_1_vi = unsafe { ::core::intrinsics::discriminant_value(&*other) } as isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&Call::System(ref __self_0), &Call::System(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Call::Babe(ref __self_0), &Call::Babe(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Call::Timestamp(ref __self_0), &Call::Timestamp(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Call::Authorship(ref __self_0), &Call::Authorship(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Call::Indices(ref __self_0), &Call::Indices(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Call::Balances(ref __self_0), &Call::Balances(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Call::Staking(ref __self_0), &Call::Staking(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Call::Session(ref __self_0), &Call::Session(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Call::Democracy(ref __self_0), &Call::Democracy(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Call::Council(ref __self_0), &Call::Council(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (
                        &Call::TechnicalCommittee(ref __self_0),
                        &Call::TechnicalCommittee(ref __arg_1_0),
                    ) => (*__self_0) == (*__arg_1_0),
                    (&Call::Elections(ref __self_0), &Call::Elections(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (
                        &Call::TechnicalMembership(ref __self_0),
                        &Call::TechnicalMembership(ref __arg_1_0),
                    ) => (*__self_0) == (*__arg_1_0),
                    (
                        &Call::FinalityTracker(ref __self_0),
                        &Call::FinalityTracker(ref __arg_1_0),
                    ) => (*__self_0) == (*__arg_1_0),
                    (&Call::Grandpa(ref __self_0), &Call::Grandpa(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Call::Treasury(ref __self_0), &Call::Treasury(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Call::Contracts(ref __self_0), &Call::Contracts(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Call::Sudo(ref __self_0), &Call::Sudo(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Call::ImOnline(ref __self_0), &Call::ImOnline(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (
                        &Call::AuthorityDiscovery(ref __self_0),
                        &Call::AuthorityDiscovery(ref __arg_1_0),
                    ) => (*__self_0) == (*__arg_1_0),
                    (&Call::Offences(ref __self_0), &Call::Offences(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    (&Call::Bridge(ref __self_0), &Call::Bridge(ref __arg_1_0)) => {
                        (*__self_0) == (*__arg_1_0)
                    }
                    _ => unsafe { ::core::intrinsics::unreachable() },
                }
            } else {
                false
            }
        }
    }
    #[inline]
    fn ne(&self, other: &Call) -> bool {
        {
            let __self_vi = unsafe { ::core::intrinsics::discriminant_value(&*self) } as isize;
            let __arg_1_vi = unsafe { ::core::intrinsics::discriminant_value(&*other) } as isize;
            if true && __self_vi == __arg_1_vi {
                match (&*self, &*other) {
                    (&Call::System(ref __self_0), &Call::System(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Call::Babe(ref __self_0), &Call::Babe(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Call::Timestamp(ref __self_0), &Call::Timestamp(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Call::Authorship(ref __self_0), &Call::Authorship(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Call::Indices(ref __self_0), &Call::Indices(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Call::Balances(ref __self_0), &Call::Balances(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Call::Staking(ref __self_0), &Call::Staking(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Call::Session(ref __self_0), &Call::Session(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Call::Democracy(ref __self_0), &Call::Democracy(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Call::Council(ref __self_0), &Call::Council(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (
                        &Call::TechnicalCommittee(ref __self_0),
                        &Call::TechnicalCommittee(ref __arg_1_0),
                    ) => (*__self_0) != (*__arg_1_0),
                    (&Call::Elections(ref __self_0), &Call::Elections(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (
                        &Call::TechnicalMembership(ref __self_0),
                        &Call::TechnicalMembership(ref __arg_1_0),
                    ) => (*__self_0) != (*__arg_1_0),
                    (
                        &Call::FinalityTracker(ref __self_0),
                        &Call::FinalityTracker(ref __arg_1_0),
                    ) => (*__self_0) != (*__arg_1_0),
                    (&Call::Grandpa(ref __self_0), &Call::Grandpa(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Call::Treasury(ref __self_0), &Call::Treasury(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Call::Contracts(ref __self_0), &Call::Contracts(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Call::Sudo(ref __self_0), &Call::Sudo(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Call::ImOnline(ref __self_0), &Call::ImOnline(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (
                        &Call::AuthorityDiscovery(ref __self_0),
                        &Call::AuthorityDiscovery(ref __arg_1_0),
                    ) => (*__self_0) != (*__arg_1_0),
                    (&Call::Offences(ref __self_0), &Call::Offences(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    (&Call::Bridge(ref __self_0), &Call::Bridge(ref __arg_1_0)) => {
                        (*__self_0) != (*__arg_1_0)
                    }
                    _ => unsafe { ::core::intrinsics::unreachable() },
                }
            } else {
                true
            }
        }
    }
}
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::core::cmp::Eq for Call {
    #[inline]
    #[doc(hidden)]
    fn assert_receiver_is_total_eq(&self) -> () {
        {
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<System, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Babe, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Timestamp, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Authorship, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Indices, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Balances, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Staking, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Session, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Democracy, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Council, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<TechnicalCommittee, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Elections, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<TechnicalMembership, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<FinalityTracker, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Grandpa, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Treasury, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Contracts, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Sudo, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<ImOnline, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<AuthorityDiscovery, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Offences, Runtime>,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                ::srml_support::dispatch::CallableCallFor<Bridge, Runtime>,
            >;
        }
    }
}
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_ENCODE_FOR_Call: () = {
    #[allow(unknown_lints)]
    #[allow(rust_2018_idioms)]
    extern crate codec as _parity_scale_codec;
    impl _parity_scale_codec::Encode for Call {
        fn encode_to<EncOut: _parity_scale_codec::Output>(&self, dest: &mut EncOut) {
            match *self {
                Call::System(ref aa) => {
                    dest.push_byte(0usize as u8);
                    dest.push(aa);
                }
                Call::Babe(ref aa) => {
                    dest.push_byte(1usize as u8);
                    dest.push(aa);
                }
                Call::Timestamp(ref aa) => {
                    dest.push_byte(2usize as u8);
                    dest.push(aa);
                }
                Call::Authorship(ref aa) => {
                    dest.push_byte(3usize as u8);
                    dest.push(aa);
                }
                Call::Indices(ref aa) => {
                    dest.push_byte(4usize as u8);
                    dest.push(aa);
                }
                Call::Balances(ref aa) => {
                    dest.push_byte(5usize as u8);
                    dest.push(aa);
                }
                Call::Staking(ref aa) => {
                    dest.push_byte(6usize as u8);
                    dest.push(aa);
                }
                Call::Session(ref aa) => {
                    dest.push_byte(7usize as u8);
                    dest.push(aa);
                }
                Call::Democracy(ref aa) => {
                    dest.push_byte(8usize as u8);
                    dest.push(aa);
                }
                Call::Council(ref aa) => {
                    dest.push_byte(9usize as u8);
                    dest.push(aa);
                }
                Call::TechnicalCommittee(ref aa) => {
                    dest.push_byte(10usize as u8);
                    dest.push(aa);
                }
                Call::Elections(ref aa) => {
                    dest.push_byte(11usize as u8);
                    dest.push(aa);
                }
                Call::TechnicalMembership(ref aa) => {
                    dest.push_byte(12usize as u8);
                    dest.push(aa);
                }
                Call::FinalityTracker(ref aa) => {
                    dest.push_byte(13usize as u8);
                    dest.push(aa);
                }
                Call::Grandpa(ref aa) => {
                    dest.push_byte(14usize as u8);
                    dest.push(aa);
                }
                Call::Treasury(ref aa) => {
                    dest.push_byte(15usize as u8);
                    dest.push(aa);
                }
                Call::Contracts(ref aa) => {
                    dest.push_byte(16usize as u8);
                    dest.push(aa);
                }
                Call::Sudo(ref aa) => {
                    dest.push_byte(17usize as u8);
                    dest.push(aa);
                }
                Call::ImOnline(ref aa) => {
                    dest.push_byte(18usize as u8);
                    dest.push(aa);
                }
                Call::AuthorityDiscovery(ref aa) => {
                    dest.push_byte(19usize as u8);
                    dest.push(aa);
                }
                Call::Offences(ref aa) => {
                    dest.push_byte(20usize as u8);
                    dest.push(aa);
                }
                Call::Bridge(ref aa) => {
                    dest.push_byte(21usize as u8);
                    dest.push(aa);
                }
                _ => (),
            }
        }
    }
    impl _parity_scale_codec::EncodeLike for Call {}
};
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_DECODE_FOR_Call: () = {
    #[allow(unknown_lints)]
    #[allow(rust_2018_idioms)]
    extern crate codec as _parity_scale_codec;
    impl _parity_scale_codec::Decode for Call {
        fn decode<DecIn: _parity_scale_codec::Input>(
            input: &mut DecIn,
        ) -> core::result::Result<Self, _parity_scale_codec::Error> {
            match input.read_byte()? {
                x if x == 0usize as u8 => Ok(Call::System({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: System.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 1usize as u8 => Ok(Call::Babe({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Babe.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 2usize as u8 => Ok(Call::Timestamp({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Timestamp.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 3usize as u8 => Ok(Call::Authorship({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Authorship.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 4usize as u8 => Ok(Call::Indices({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Indices.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 5usize as u8 => Ok(Call::Balances({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Balances.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 6usize as u8 => Ok(Call::Staking({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Staking.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 7usize as u8 => Ok(Call::Session({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Session.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 8usize as u8 => Ok(Call::Democracy({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Democracy.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 9usize as u8 => Ok(Call::Council({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Council.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 10usize as u8 => Ok(Call::TechnicalCommittee({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => {
                            return Err("Error decoding field Call :: TechnicalCommittee.0".into())
                        }
                        Ok(a) => a,
                    }
                })),
                x if x == 11usize as u8 => Ok(Call::Elections({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Elections.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 12usize as u8 => Ok(Call::TechnicalMembership({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => {
                            return Err("Error decoding field Call :: TechnicalMembership.0".into())
                        }
                        Ok(a) => a,
                    }
                })),
                x if x == 13usize as u8 => Ok(Call::FinalityTracker({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => {
                            return Err("Error decoding field Call :: FinalityTracker.0".into())
                        }
                        Ok(a) => a,
                    }
                })),
                x if x == 14usize as u8 => Ok(Call::Grandpa({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Grandpa.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 15usize as u8 => Ok(Call::Treasury({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Treasury.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 16usize as u8 => Ok(Call::Contracts({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Contracts.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 17usize as u8 => Ok(Call::Sudo({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Sudo.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 18usize as u8 => Ok(Call::ImOnline({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: ImOnline.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 19usize as u8 => Ok(Call::AuthorityDiscovery({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => {
                            return Err("Error decoding field Call :: AuthorityDiscovery.0".into())
                        }
                        Ok(a) => a,
                    }
                })),
                x if x == 20usize as u8 => Ok(Call::Offences({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Offences.0".into()),
                        Ok(a) => a,
                    }
                })),
                x if x == 21usize as u8 => Ok(Call::Bridge({
                    let res = _parity_scale_codec::Decode::decode(input);
                    match res {
                        Err(_) => return Err("Error decoding field Call :: Bridge.0".into()),
                        Ok(a) => a,
                    }
                })),
                x => Err("No such variant in enum Call".into()),
            }
        }
    }
};
#[automatically_derived]
#[allow(unused_qualifications)]
impl ::core::fmt::Debug for Call {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        match (&*self,) {
            (&Call::System(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("System");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Babe(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Babe");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Timestamp(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Timestamp");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Authorship(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Authorship");
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
            (&Call::Staking(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Staking");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Session(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Session");
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
            (&Call::TechnicalCommittee(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("TechnicalCommittee");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Elections(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Elections");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::TechnicalMembership(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("TechnicalMembership");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::FinalityTracker(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("FinalityTracker");
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
            (&Call::Contracts(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Contracts");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Sudo(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Sudo");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::ImOnline(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("ImOnline");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::AuthorityDiscovery(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("AuthorityDiscovery");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Offences(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Offences");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
            (&Call::Bridge(ref __self_0),) => {
                let mut debug_trait_builder = f.debug_tuple("Bridge");
                let _ = debug_trait_builder.field(&&(*__self_0));
                debug_trait_builder.finish()
            }
        }
    }
}
impl ::srml_support::dispatch::GetDispatchInfo for Call {
    fn get_dispatch_info(&self) -> ::srml_support::dispatch::DispatchInfo {
        match self {
            Call::System(call) => call.get_dispatch_info(),
            Call::Babe(call) => call.get_dispatch_info(),
            Call::Timestamp(call) => call.get_dispatch_info(),
            Call::Authorship(call) => call.get_dispatch_info(),
            Call::Indices(call) => call.get_dispatch_info(),
            Call::Balances(call) => call.get_dispatch_info(),
            Call::Staking(call) => call.get_dispatch_info(),
            Call::Session(call) => call.get_dispatch_info(),
            Call::Democracy(call) => call.get_dispatch_info(),
            Call::Council(call) => call.get_dispatch_info(),
            Call::TechnicalCommittee(call) => call.get_dispatch_info(),
            Call::Elections(call) => call.get_dispatch_info(),
            Call::TechnicalMembership(call) => call.get_dispatch_info(),
            Call::FinalityTracker(call) => call.get_dispatch_info(),
            Call::Grandpa(call) => call.get_dispatch_info(),
            Call::Treasury(call) => call.get_dispatch_info(),
            Call::Contracts(call) => call.get_dispatch_info(),
            Call::Sudo(call) => call.get_dispatch_info(),
            Call::ImOnline(call) => call.get_dispatch_info(),
            Call::AuthorityDiscovery(call) => call.get_dispatch_info(),
            Call::Offences(call) => call.get_dispatch_info(),
            Call::Bridge(call) => call.get_dispatch_info(),
        }
    }
}
impl ::srml_support::dispatch::Dispatchable for Call {
    type Origin = Origin;
    type Trait = Call;
    type Error = ::srml_support::dispatch::DispatchError;
    fn dispatch(
        self,
        origin: Origin,
    ) -> ::srml_support::dispatch::DispatchResult<::srml_support::dispatch::DispatchError> {
        match self {
            Call::System(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0);
                error
            }),
            Call::Babe(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0 + 1);
                error
            }),
            Call::Timestamp(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0 + 1 + 1);
                error
            }),
            Call::Authorship(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0 + 1 + 1 + 1);
                error
            }),
            Call::Indices(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0 + 1 + 1 + 1 + 1);
                error
            }),
            Call::Balances(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0 + 1 + 1 + 1 + 1 + 1);
                error
            }),
            Call::Staking(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0 + 1 + 1 + 1 + 1 + 1 + 1);
                error
            }),
            Call::Session(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0 + 1 + 1 + 1 + 1 + 1 + 1 + 1);
                error
            }),
            Call::Democracy(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1);
                error
            }),
            Call::Council(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1);
                error
            }),
            Call::TechnicalCommittee(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1);
                error
            }),
            Call::Elections(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1);
                error
            }),
            Call::TechnicalMembership(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1);
                error
            }),
            Call::FinalityTracker(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1);
                error
            }),
            Call::Grandpa(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1);
                error
            }),
            Call::Treasury(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1);
                error
            }),
            Call::Contracts(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module =
                    Some(0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1);
                error
            }),
            Call::Sudo(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module =
                    Some(0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1);
                error
            }),
            Call::ImOnline(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module =
                    Some(0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1);
                error
            }),
            Call::AuthorityDiscovery(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(
                    0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1,
                );
                error
            }),
            Call::Offences(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(
                    0 + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1,
                );
                error
            }),
            Call::Bridge(call) => call.dispatch(origin).map_err(|e| {
                let mut error: ::srml_support::dispatch::DispatchError = e.into();
                error.module = Some(
                    0 + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1
                        + 1,
                );
                error
            }),
        }
    }
}
impl ::srml_support::dispatch::IsSubType<System, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(&self) -> Option<&::srml_support::dispatch::CallableCallFor<System, Runtime>> {
        match *self {
            Call::System(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<System, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<System, Runtime>) -> Self {
        Call::System(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Babe, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(&self) -> Option<&::srml_support::dispatch::CallableCallFor<Babe, Runtime>> {
        match *self {
            Call::Babe(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Babe, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Babe, Runtime>) -> Self {
        Call::Babe(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Timestamp, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(
        &self,
    ) -> Option<&::srml_support::dispatch::CallableCallFor<Timestamp, Runtime>> {
        match *self {
            Call::Timestamp(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Timestamp, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Timestamp, Runtime>) -> Self {
        Call::Timestamp(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Authorship, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(
        &self,
    ) -> Option<&::srml_support::dispatch::CallableCallFor<Authorship, Runtime>> {
        match *self {
            Call::Authorship(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Authorship, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Authorship, Runtime>) -> Self {
        Call::Authorship(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Indices, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(&self) -> Option<&::srml_support::dispatch::CallableCallFor<Indices, Runtime>> {
        match *self {
            Call::Indices(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Indices, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Indices, Runtime>) -> Self {
        Call::Indices(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Balances, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(&self) -> Option<&::srml_support::dispatch::CallableCallFor<Balances, Runtime>> {
        match *self {
            Call::Balances(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Balances, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Balances, Runtime>) -> Self {
        Call::Balances(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Staking, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(&self) -> Option<&::srml_support::dispatch::CallableCallFor<Staking, Runtime>> {
        match *self {
            Call::Staking(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Staking, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Staking, Runtime>) -> Self {
        Call::Staking(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Session, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(&self) -> Option<&::srml_support::dispatch::CallableCallFor<Session, Runtime>> {
        match *self {
            Call::Session(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Session, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Session, Runtime>) -> Self {
        Call::Session(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Democracy, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(
        &self,
    ) -> Option<&::srml_support::dispatch::CallableCallFor<Democracy, Runtime>> {
        match *self {
            Call::Democracy(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Democracy, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Democracy, Runtime>) -> Self {
        Call::Democracy(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Council, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(&self) -> Option<&::srml_support::dispatch::CallableCallFor<Council, Runtime>> {
        match *self {
            Call::Council(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Council, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Council, Runtime>) -> Self {
        Call::Council(call)
    }
}
impl ::srml_support::dispatch::IsSubType<TechnicalCommittee, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(
        &self,
    ) -> Option<&::srml_support::dispatch::CallableCallFor<TechnicalCommittee, Runtime>> {
        match *self {
            Call::TechnicalCommittee(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<TechnicalCommittee, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<TechnicalCommittee, Runtime>) -> Self {
        Call::TechnicalCommittee(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Elections, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(
        &self,
    ) -> Option<&::srml_support::dispatch::CallableCallFor<Elections, Runtime>> {
        match *self {
            Call::Elections(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Elections, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Elections, Runtime>) -> Self {
        Call::Elections(call)
    }
}
impl ::srml_support::dispatch::IsSubType<TechnicalMembership, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(
        &self,
    ) -> Option<&::srml_support::dispatch::CallableCallFor<TechnicalMembership, Runtime>> {
        match *self {
            Call::TechnicalMembership(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<TechnicalMembership, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<TechnicalMembership, Runtime>) -> Self {
        Call::TechnicalMembership(call)
    }
}
impl ::srml_support::dispatch::IsSubType<FinalityTracker, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(
        &self,
    ) -> Option<&::srml_support::dispatch::CallableCallFor<FinalityTracker, Runtime>> {
        match *self {
            Call::FinalityTracker(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<FinalityTracker, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<FinalityTracker, Runtime>) -> Self {
        Call::FinalityTracker(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Grandpa, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(&self) -> Option<&::srml_support::dispatch::CallableCallFor<Grandpa, Runtime>> {
        match *self {
            Call::Grandpa(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Grandpa, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Grandpa, Runtime>) -> Self {
        Call::Grandpa(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Treasury, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(&self) -> Option<&::srml_support::dispatch::CallableCallFor<Treasury, Runtime>> {
        match *self {
            Call::Treasury(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Treasury, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Treasury, Runtime>) -> Self {
        Call::Treasury(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Contracts, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(
        &self,
    ) -> Option<&::srml_support::dispatch::CallableCallFor<Contracts, Runtime>> {
        match *self {
            Call::Contracts(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Contracts, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Contracts, Runtime>) -> Self {
        Call::Contracts(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Sudo, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(&self) -> Option<&::srml_support::dispatch::CallableCallFor<Sudo, Runtime>> {
        match *self {
            Call::Sudo(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Sudo, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Sudo, Runtime>) -> Self {
        Call::Sudo(call)
    }
}
impl ::srml_support::dispatch::IsSubType<ImOnline, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(&self) -> Option<&::srml_support::dispatch::CallableCallFor<ImOnline, Runtime>> {
        match *self {
            Call::ImOnline(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<ImOnline, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<ImOnline, Runtime>) -> Self {
        Call::ImOnline(call)
    }
}
impl ::srml_support::dispatch::IsSubType<AuthorityDiscovery, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(
        &self,
    ) -> Option<&::srml_support::dispatch::CallableCallFor<AuthorityDiscovery, Runtime>> {
        match *self {
            Call::AuthorityDiscovery(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<AuthorityDiscovery, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<AuthorityDiscovery, Runtime>) -> Self {
        Call::AuthorityDiscovery(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Offences, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(&self) -> Option<&::srml_support::dispatch::CallableCallFor<Offences, Runtime>> {
        match *self {
            Call::Offences(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Offences, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Offences, Runtime>) -> Self {
        Call::Offences(call)
    }
}
impl ::srml_support::dispatch::IsSubType<Bridge, Runtime> for Call {
    #[allow(unreachable_patterns)]
    fn is_sub_type(&self) -> Option<&::srml_support::dispatch::CallableCallFor<Bridge, Runtime>> {
        match *self {
            Call::Bridge(ref r) => Some(r),
            _ => None,
        }
    }
}
impl From<::srml_support::dispatch::CallableCallFor<Bridge, Runtime>> for Call {
    fn from(call: ::srml_support::dispatch::CallableCallFor<Bridge, Runtime>) -> Self {
        Call::Bridge(call)
    }
}
impl Runtime {
    pub fn metadata() -> ::srml_support::metadata::RuntimeMetadataPrefixed {
        :: srml_support :: metadata :: RuntimeMetadataLastVersion { modules : :: srml_support :: metadata :: DecodeDifferent :: Encode ( & [ :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "System" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( system :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( system :: Module :: < Runtime > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ system >]" , 0 ) . 1 , } { Runtime :: __module_events_system } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( system :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Babe" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( babe :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( babe :: Module :: < Runtime > :: call_functions ) ) ) , event : None , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( babe :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Timestamp" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( timestamp :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( timestamp :: Module :: < Runtime > :: call_functions ) ) ) , event : None , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( timestamp :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Authorship" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( authorship :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( authorship :: Module :: < Runtime > :: call_functions ) ) ) , event : None , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( authorship :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Indices" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( indices :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( indices :: Module :: < Runtime > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ indices >]" , 0 ) . 1 , } { Runtime :: __module_events_indices } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( indices :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Balances" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( balances :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( balances :: Module :: < Runtime > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ balances >]" , 0 ) . 1 , } { Runtime :: __module_events_balances } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( balances :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Staking" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( staking :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( staking :: Module :: < Runtime > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ staking >]" , 0 ) . 1 , } { Runtime :: __module_events_staking } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( staking :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Session" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( session :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( session :: Module :: < Runtime > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ session >]" , 0 ) . 1 , } { Runtime :: __module_events_session } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( session :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Democracy" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( democracy :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( democracy :: Module :: < Runtime > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ democracy >]" , 0 ) . 1 , } { Runtime :: __module_events_democracy } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( democracy :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Council" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( collective :: Module :: < Runtime , collective :: Instance1 > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( collective :: Module :: < Runtime , collective :: Instance1 > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ collective _ Instance1 >]" , 0 ) . 1 , } { Runtime :: __module_events_collective_Instance1 } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( collective :: Module :: < Runtime , collective :: Instance1 > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "TechnicalCommittee" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( collective :: Module :: < Runtime , collective :: Instance2 > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( collective :: Module :: < Runtime , collective :: Instance2 > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ collective _ Instance2 >]" , 0 ) . 1 , } { Runtime :: __module_events_collective_Instance2 } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( collective :: Module :: < Runtime , collective :: Instance2 > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Elections" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( elections :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( elections :: Module :: < Runtime > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ elections >]" , 0 ) . 1 , } { Runtime :: __module_events_elections } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( elections :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "TechnicalMembership" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( membership :: Module :: < Runtime , membership :: Instance1 > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( membership :: Module :: < Runtime , membership :: Instance1 > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ membership _ Instance1 >]" , 0 ) . 1 , } { Runtime :: __module_events_membership_Instance1 } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( membership :: Module :: < Runtime , membership :: Instance1 > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "FinalityTracker" ) , storage : None , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( finality_tracker :: Module :: < Runtime > :: call_functions ) ) ) , event : None , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( finality_tracker :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Grandpa" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( grandpa :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( grandpa :: Module :: < Runtime > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ grandpa >]" , 0 ) . 1 , } { Runtime :: __module_events_grandpa } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( grandpa :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Treasury" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( treasury :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( treasury :: Module :: < Runtime > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ treasury >]" , 0 ) . 1 , } { Runtime :: __module_events_treasury } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( treasury :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Contracts" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( contracts :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( contracts :: Module :: < Runtime > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ contracts >]" , 0 ) . 1 , } { Runtime :: __module_events_contracts } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( contracts :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Sudo" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( sudo :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( sudo :: Module :: < Runtime > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ sudo >]" , 0 ) . 1 , } { Runtime :: __module_events_sudo } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( sudo :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "ImOnline" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( im_online :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( im_online :: Module :: < Runtime > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ im_online >]" , 0 ) . 1 , } { Runtime :: __module_events_im_online } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( im_online :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "AuthorityDiscovery" ) , storage : None , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( authority_discovery :: Module :: < Runtime > :: call_functions ) ) ) , event : None , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( authority_discovery :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Offences" ) , storage : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( offences :: Module :: < Runtime > :: storage_metadata ) ) ) , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( offences :: Module :: < Runtime > :: call_functions ) ) ) , event : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( { enum ProcMacroHack { Value = ( "Runtime :: [< __module_events_ offences >]" , 0 ) . 1 , } { Runtime :: __module_events_offences } } ) ) ) , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( offences :: Module :: < Runtime > :: module_constants_metadata ) ) , } , :: srml_support :: metadata :: ModuleMetadata { name : :: srml_support :: metadata :: DecodeDifferent :: Encode ( "Bridge" ) , storage : None , calls : Some ( :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( bridge :: Module :: < Runtime > :: call_functions ) ) ) , event : None , constants : :: srml_support :: metadata :: DecodeDifferent :: Encode ( :: srml_support :: metadata :: FnEncode ( bridge :: Module :: < Runtime > :: module_constants_metadata ) ) , } ] ) , } . into ( )
    }
}
#[cfg(any(feature = "std", test))]
pub type SystemConfig = system::GenesisConfig;
#[cfg(any(feature = "std", test))]
pub type BabeConfig = babe::GenesisConfig;
#[cfg(any(feature = "std", test))]
pub type IndicesConfig = indices::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type BalancesConfig = balances::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type StakingConfig = staking::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type SessionConfig = session::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type DemocracyConfig = democracy::GenesisConfig;
#[cfg(any(feature = "std", test))]
pub type CouncilConfig = collective::GenesisConfig<Runtime, collective::Instance1>;
#[cfg(any(feature = "std", test))]
pub type TechnicalCommitteeConfig = collective::GenesisConfig<Runtime, collective::Instance2>;
#[cfg(any(feature = "std", test))]
pub type ElectionsConfig = elections::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type TechnicalMembershipConfig = membership::GenesisConfig<Runtime, membership::Instance1>;
#[cfg(any(feature = "std", test))]
pub type GrandpaConfig = grandpa::GenesisConfig;
#[cfg(any(feature = "std", test))]
pub type ContractsConfig = contracts::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type SudoConfig = sudo::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type ImOnlineConfig = im_online::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
pub type AuthorityDiscoveryConfig = authority_discovery::GenesisConfig<Runtime>;
#[cfg(any(feature = "std", test))]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct GenesisConfig {
    pub system: Option<SystemConfig>,
    pub babe: Option<BabeConfig>,
    pub indices: Option<IndicesConfig>,
    pub balances: Option<BalancesConfig>,
    pub staking: Option<StakingConfig>,
    pub session: Option<SessionConfig>,
    pub democracy: Option<DemocracyConfig>,
    pub collective_Instance1: Option<CouncilConfig>,
    pub collective_Instance2: Option<TechnicalCommitteeConfig>,
    pub elections: Option<ElectionsConfig>,
    pub membership_Instance1: Option<TechnicalMembershipConfig>,
    pub grandpa: Option<GrandpaConfig>,
    pub contracts: Option<ContractsConfig>,
    pub sudo: Option<SudoConfig>,
    pub im_online: Option<ImOnlineConfig>,
    pub authority_discovery: Option<AuthorityDiscoveryConfig>,
}
#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
const _IMPL_SERIALIZE_FOR_GenesisConfig: () = {
    #[allow(unknown_lints)]
    #[allow(rust_2018_idioms)]
    extern crate serde as _serde;
    #[automatically_derived]
    impl _serde::Serialize for GenesisConfig {
        fn serialize<__S>(&self, __serializer: __S) -> _serde::export::Result<__S::Ok, __S::Error>
        where
            __S: _serde::Serializer,
        {
            let mut __serde_state = match _serde::Serializer::serialize_struct(
                __serializer,
                "GenesisConfig",
                false as usize + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "system",
                &self.system,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "babe",
                &self.babe,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "indices",
                &self.indices,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "balances",
                &self.balances,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "staking",
                &self.staking,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "session",
                &self.session,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "democracy",
                &self.democracy,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "collectiveInstance1",
                &self.collective_Instance1,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "collectiveInstance2",
                &self.collective_Instance2,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "elections",
                &self.elections,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "membershipInstance1",
                &self.membership_Instance1,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "grandpa",
                &self.grandpa,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "contracts",
                &self.contracts,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "sudo",
                &self.sudo,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "imOnline",
                &self.im_online,
            ) {
                _serde::export::Ok(__val) => __val,
                _serde::export::Err(__err) => {
                    return _serde::export::Err(__err);
                }
            };
            match _serde::ser::SerializeStruct::serialize_field(
                &mut __serde_state,
                "authorityDiscovery",
                &self.authority_discovery,
            ) {
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
const _IMPL_DESERIALIZE_FOR_GenesisConfig: () = {
    #[allow(unknown_lints)]
    #[allow(rust_2018_idioms)]
    extern crate serde as _serde;
    #[automatically_derived]
    impl<'de> _serde::Deserialize<'de> for GenesisConfig {
        fn deserialize<__D>(__deserializer: __D) -> _serde::export::Result<Self, __D::Error>
        where
            __D: _serde::Deserializer<'de>,
        {
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
                __field14,
                __field15,
            }
            struct __FieldVisitor;
            impl<'de> _serde::de::Visitor<'de> for __FieldVisitor {
                type Value = __Field;
                fn expecting(
                    &self,
                    __formatter: &mut _serde::export::Formatter,
                ) -> _serde::export::fmt::Result {
                    _serde::export::Formatter::write_str(__formatter, "field identifier")
                }
                fn visit_u64<__E>(self, __value: u64) -> _serde::export::Result<Self::Value, __E>
                where
                    __E: _serde::de::Error,
                {
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
                        14u64 => _serde::export::Ok(__Field::__field14),
                        15u64 => _serde::export::Ok(__Field::__field15),
                        _ => _serde::export::Err(_serde::de::Error::invalid_value(
                            _serde::de::Unexpected::Unsigned(__value),
                            &"field index 0 <= i < 16",
                        )),
                    }
                }
                fn visit_str<__E>(self, __value: &str) -> _serde::export::Result<Self::Value, __E>
                where
                    __E: _serde::de::Error,
                {
                    match __value {
                        "system" => _serde::export::Ok(__Field::__field0),
                        "babe" => _serde::export::Ok(__Field::__field1),
                        "indices" => _serde::export::Ok(__Field::__field2),
                        "balances" => _serde::export::Ok(__Field::__field3),
                        "staking" => _serde::export::Ok(__Field::__field4),
                        "session" => _serde::export::Ok(__Field::__field5),
                        "democracy" => _serde::export::Ok(__Field::__field6),
                        "collectiveInstance1" => _serde::export::Ok(__Field::__field7),
                        "collectiveInstance2" => _serde::export::Ok(__Field::__field8),
                        "elections" => _serde::export::Ok(__Field::__field9),
                        "membershipInstance1" => _serde::export::Ok(__Field::__field10),
                        "grandpa" => _serde::export::Ok(__Field::__field11),
                        "contracts" => _serde::export::Ok(__Field::__field12),
                        "sudo" => _serde::export::Ok(__Field::__field13),
                        "imOnline" => _serde::export::Ok(__Field::__field14),
                        "authorityDiscovery" => _serde::export::Ok(__Field::__field15),
                        _ => _serde::export::Err(_serde::de::Error::unknown_field(__value, FIELDS)),
                    }
                }
                fn visit_bytes<__E>(
                    self,
                    __value: &[u8],
                ) -> _serde::export::Result<Self::Value, __E>
                where
                    __E: _serde::de::Error,
                {
                    match __value {
                        b"system" => _serde::export::Ok(__Field::__field0),
                        b"babe" => _serde::export::Ok(__Field::__field1),
                        b"indices" => _serde::export::Ok(__Field::__field2),
                        b"balances" => _serde::export::Ok(__Field::__field3),
                        b"staking" => _serde::export::Ok(__Field::__field4),
                        b"session" => _serde::export::Ok(__Field::__field5),
                        b"democracy" => _serde::export::Ok(__Field::__field6),
                        b"collectiveInstance1" => _serde::export::Ok(__Field::__field7),
                        b"collectiveInstance2" => _serde::export::Ok(__Field::__field8),
                        b"elections" => _serde::export::Ok(__Field::__field9),
                        b"membershipInstance1" => _serde::export::Ok(__Field::__field10),
                        b"grandpa" => _serde::export::Ok(__Field::__field11),
                        b"contracts" => _serde::export::Ok(__Field::__field12),
                        b"sudo" => _serde::export::Ok(__Field::__field13),
                        b"imOnline" => _serde::export::Ok(__Field::__field14),
                        b"authorityDiscovery" => _serde::export::Ok(__Field::__field15),
                        _ => {
                            let __value = &_serde::export::from_utf8_lossy(__value);
                            _serde::export::Err(_serde::de::Error::unknown_field(__value, FIELDS))
                        }
                    }
                }
            }
            impl<'de> _serde::Deserialize<'de> for __Field {
                #[inline]
                fn deserialize<__D>(__deserializer: __D) -> _serde::export::Result<Self, __D::Error>
                where
                    __D: _serde::Deserializer<'de>,
                {
                    _serde::Deserializer::deserialize_identifier(__deserializer, __FieldVisitor)
                }
            }
            struct __Visitor<'de> {
                marker: _serde::export::PhantomData<GenesisConfig>,
                lifetime: _serde::export::PhantomData<&'de ()>,
            }
            impl<'de> _serde::de::Visitor<'de> for __Visitor<'de> {
                type Value = GenesisConfig;
                fn expecting(
                    &self,
                    __formatter: &mut _serde::export::Formatter,
                ) -> _serde::export::fmt::Result {
                    _serde::export::Formatter::write_str(__formatter, "struct GenesisConfig")
                }
                #[inline]
                fn visit_seq<__A>(
                    self,
                    mut __seq: __A,
                ) -> _serde::export::Result<Self::Value, __A::Error>
                where
                    __A: _serde::de::SeqAccess<'de>,
                {
                    let __field0 = match match _serde::de::SeqAccess::next_element::<
                        Option<SystemConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                0usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    let __field1 = match match _serde::de::SeqAccess::next_element::<
                        Option<BabeConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                1usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    let __field2 = match match _serde::de::SeqAccess::next_element::<
                        Option<IndicesConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                2usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    let __field3 = match match _serde::de::SeqAccess::next_element::<
                        Option<BalancesConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                3usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    let __field4 = match match _serde::de::SeqAccess::next_element::<
                        Option<StakingConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                4usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    let __field5 = match match _serde::de::SeqAccess::next_element::<
                        Option<SessionConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                5usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    let __field6 = match match _serde::de::SeqAccess::next_element::<
                        Option<DemocracyConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                6usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    let __field7 = match match _serde::de::SeqAccess::next_element::<
                        Option<CouncilConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                7usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    let __field8 = match match _serde::de::SeqAccess::next_element::<
                        Option<TechnicalCommitteeConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                8usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    let __field9 = match match _serde::de::SeqAccess::next_element::<
                        Option<ElectionsConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                9usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    let __field10 = match match _serde::de::SeqAccess::next_element::<
                        Option<TechnicalMembershipConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                10usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    let __field11 = match match _serde::de::SeqAccess::next_element::<
                        Option<GrandpaConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                11usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    let __field12 = match match _serde::de::SeqAccess::next_element::<
                        Option<ContractsConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                12usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    let __field13 = match match _serde::de::SeqAccess::next_element::<
                        Option<SudoConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                13usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    let __field14 = match match _serde::de::SeqAccess::next_element::<
                        Option<ImOnlineConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                14usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    let __field15 = match match _serde::de::SeqAccess::next_element::<
                        Option<AuthorityDiscoveryConfig>,
                    >(&mut __seq)
                    {
                        _serde::export::Ok(__val) => __val,
                        _serde::export::Err(__err) => {
                            return _serde::export::Err(__err);
                        }
                    } {
                        _serde::export::Some(__value) => __value,
                        _serde::export::None => {
                            return _serde::export::Err(_serde::de::Error::invalid_length(
                                15usize,
                                &"struct GenesisConfig with 16 elements",
                            ));
                        }
                    };
                    _serde::export::Ok(GenesisConfig {
                        system: __field0,
                        babe: __field1,
                        indices: __field2,
                        balances: __field3,
                        staking: __field4,
                        session: __field5,
                        democracy: __field6,
                        collective_Instance1: __field7,
                        collective_Instance2: __field8,
                        elections: __field9,
                        membership_Instance1: __field10,
                        grandpa: __field11,
                        contracts: __field12,
                        sudo: __field13,
                        im_online: __field14,
                        authority_discovery: __field15,
                    })
                }
                #[inline]
                fn visit_map<__A>(
                    self,
                    mut __map: __A,
                ) -> _serde::export::Result<Self::Value, __A::Error>
                where
                    __A: _serde::de::MapAccess<'de>,
                {
                    let mut __field0: _serde::export::Option<Option<SystemConfig>> =
                        _serde::export::None;
                    let mut __field1: _serde::export::Option<Option<BabeConfig>> =
                        _serde::export::None;
                    let mut __field2: _serde::export::Option<Option<IndicesConfig>> =
                        _serde::export::None;
                    let mut __field3: _serde::export::Option<Option<BalancesConfig>> =
                        _serde::export::None;
                    let mut __field4: _serde::export::Option<Option<StakingConfig>> =
                        _serde::export::None;
                    let mut __field5: _serde::export::Option<Option<SessionConfig>> =
                        _serde::export::None;
                    let mut __field6: _serde::export::Option<Option<DemocracyConfig>> =
                        _serde::export::None;
                    let mut __field7: _serde::export::Option<Option<CouncilConfig>> =
                        _serde::export::None;
                    let mut __field8: _serde::export::Option<Option<TechnicalCommitteeConfig>> =
                        _serde::export::None;
                    let mut __field9: _serde::export::Option<Option<ElectionsConfig>> =
                        _serde::export::None;
                    let mut __field10: _serde::export::Option<Option<TechnicalMembershipConfig>> =
                        _serde::export::None;
                    let mut __field11: _serde::export::Option<Option<GrandpaConfig>> =
                        _serde::export::None;
                    let mut __field12: _serde::export::Option<Option<ContractsConfig>> =
                        _serde::export::None;
                    let mut __field13: _serde::export::Option<Option<SudoConfig>> =
                        _serde::export::None;
                    let mut __field14: _serde::export::Option<Option<ImOnlineConfig>> =
                        _serde::export::None;
                    let mut __field15: _serde::export::Option<Option<AuthorityDiscoveryConfig>> =
                        _serde::export::None;
                    while let _serde::export::Some(__key) =
                        match _serde::de::MapAccess::next_key::<__Field>(&mut __map) {
                            _serde::export::Ok(__val) => __val,
                            _serde::export::Err(__err) => {
                                return _serde::export::Err(__err);
                            }
                        }
                    {
                        match __key {
                            __Field::__field0 => {
                                if _serde::export::Option::is_some(&__field0) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field(
                                            "system",
                                        ),
                                    );
                                }
                                __field0 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<Option<SystemConfig>>(
                                        &mut __map,
                                    ) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                            __Field::__field1 => {
                                if _serde::export::Option::is_some(&__field1) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field("babe"),
                                    );
                                }
                                __field1 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<Option<BabeConfig>>(
                                        &mut __map,
                                    ) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                            __Field::__field2 => {
                                if _serde::export::Option::is_some(&__field2) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field(
                                            "indices",
                                        ),
                                    );
                                }
                                __field2 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<Option<IndicesConfig>>(
                                        &mut __map,
                                    ) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                            __Field::__field3 => {
                                if _serde::export::Option::is_some(&__field3) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field(
                                            "balances",
                                        ),
                                    );
                                }
                                __field3 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<Option<BalancesConfig>>(
                                        &mut __map,
                                    ) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                            __Field::__field4 => {
                                if _serde::export::Option::is_some(&__field4) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field(
                                            "staking",
                                        ),
                                    );
                                }
                                __field4 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<Option<StakingConfig>>(
                                        &mut __map,
                                    ) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                            __Field::__field5 => {
                                if _serde::export::Option::is_some(&__field5) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field(
                                            "session",
                                        ),
                                    );
                                }
                                __field5 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<Option<SessionConfig>>(
                                        &mut __map,
                                    ) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                            __Field::__field6 => {
                                if _serde::export::Option::is_some(&__field6) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field(
                                            "democracy",
                                        ),
                                    );
                                }
                                __field6 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<Option<DemocracyConfig>>(
                                        &mut __map,
                                    ) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                            __Field::__field7 => {
                                if _serde::export::Option::is_some(&__field7) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field(
                                            "collectiveInstance1",
                                        ),
                                    );
                                }
                                __field7 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<Option<CouncilConfig>>(
                                        &mut __map,
                                    ) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                            __Field::__field8 => {
                                if _serde::export::Option::is_some(&__field8) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field(
                                            "collectiveInstance2",
                                        ),
                                    );
                                }
                                __field8 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<
                                        Option<TechnicalCommitteeConfig>,
                                    >(&mut __map)
                                    {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                            __Field::__field9 => {
                                if _serde::export::Option::is_some(&__field9) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field(
                                            "elections",
                                        ),
                                    );
                                }
                                __field9 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<Option<ElectionsConfig>>(
                                        &mut __map,
                                    ) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                            __Field::__field10 => {
                                if _serde::export::Option::is_some(&__field10) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field(
                                            "membershipInstance1",
                                        ),
                                    );
                                }
                                __field10 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<
                                        Option<TechnicalMembershipConfig>,
                                    >(&mut __map)
                                    {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                            __Field::__field11 => {
                                if _serde::export::Option::is_some(&__field11) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field(
                                            "grandpa",
                                        ),
                                    );
                                }
                                __field11 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<Option<GrandpaConfig>>(
                                        &mut __map,
                                    ) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                            __Field::__field12 => {
                                if _serde::export::Option::is_some(&__field12) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field(
                                            "contracts",
                                        ),
                                    );
                                }
                                __field12 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<Option<ContractsConfig>>(
                                        &mut __map,
                                    ) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                            __Field::__field13 => {
                                if _serde::export::Option::is_some(&__field13) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field("sudo"),
                                    );
                                }
                                __field13 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<Option<SudoConfig>>(
                                        &mut __map,
                                    ) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                            __Field::__field14 => {
                                if _serde::export::Option::is_some(&__field14) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field(
                                            "imOnline",
                                        ),
                                    );
                                }
                                __field14 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<Option<ImOnlineConfig>>(
                                        &mut __map,
                                    ) {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                            __Field::__field15 => {
                                if _serde::export::Option::is_some(&__field15) {
                                    return _serde::export::Err(
                                        <__A::Error as _serde::de::Error>::duplicate_field(
                                            "authorityDiscovery",
                                        ),
                                    );
                                }
                                __field15 = _serde::export::Some(
                                    match _serde::de::MapAccess::next_value::<
                                        Option<AuthorityDiscoveryConfig>,
                                    >(&mut __map)
                                    {
                                        _serde::export::Ok(__val) => __val,
                                        _serde::export::Err(__err) => {
                                            return _serde::export::Err(__err);
                                        }
                                    },
                                );
                            }
                        }
                    }
                    let __field0 = match __field0 {
                        _serde::export::Some(__field0) => __field0,
                        _serde::export::None => {
                            match _serde::private::de::missing_field("system") {
                                _serde::export::Ok(__val) => __val,
                                _serde::export::Err(__err) => {
                                    return _serde::export::Err(__err);
                                }
                            }
                        }
                    };
                    let __field1 = match __field1 {
                        _serde::export::Some(__field1) => __field1,
                        _serde::export::None => match _serde::private::de::missing_field("babe") {
                            _serde::export::Ok(__val) => __val,
                            _serde::export::Err(__err) => {
                                return _serde::export::Err(__err);
                            }
                        },
                    };
                    let __field2 = match __field2 {
                        _serde::export::Some(__field2) => __field2,
                        _serde::export::None => match _serde::private::de::missing_field("indices")
                        {
                            _serde::export::Ok(__val) => __val,
                            _serde::export::Err(__err) => {
                                return _serde::export::Err(__err);
                            }
                        },
                    };
                    let __field3 = match __field3 {
                        _serde::export::Some(__field3) => __field3,
                        _serde::export::None => {
                            match _serde::private::de::missing_field("balances") {
                                _serde::export::Ok(__val) => __val,
                                _serde::export::Err(__err) => {
                                    return _serde::export::Err(__err);
                                }
                            }
                        }
                    };
                    let __field4 = match __field4 {
                        _serde::export::Some(__field4) => __field4,
                        _serde::export::None => match _serde::private::de::missing_field("staking")
                        {
                            _serde::export::Ok(__val) => __val,
                            _serde::export::Err(__err) => {
                                return _serde::export::Err(__err);
                            }
                        },
                    };
                    let __field5 = match __field5 {
                        _serde::export::Some(__field5) => __field5,
                        _serde::export::None => match _serde::private::de::missing_field("session")
                        {
                            _serde::export::Ok(__val) => __val,
                            _serde::export::Err(__err) => {
                                return _serde::export::Err(__err);
                            }
                        },
                    };
                    let __field6 = match __field6 {
                        _serde::export::Some(__field6) => __field6,
                        _serde::export::None => {
                            match _serde::private::de::missing_field("democracy") {
                                _serde::export::Ok(__val) => __val,
                                _serde::export::Err(__err) => {
                                    return _serde::export::Err(__err);
                                }
                            }
                        }
                    };
                    let __field7 = match __field7 {
                        _serde::export::Some(__field7) => __field7,
                        _serde::export::None => {
                            match _serde::private::de::missing_field("collectiveInstance1") {
                                _serde::export::Ok(__val) => __val,
                                _serde::export::Err(__err) => {
                                    return _serde::export::Err(__err);
                                }
                            }
                        }
                    };
                    let __field8 = match __field8 {
                        _serde::export::Some(__field8) => __field8,
                        _serde::export::None => {
                            match _serde::private::de::missing_field("collectiveInstance2") {
                                _serde::export::Ok(__val) => __val,
                                _serde::export::Err(__err) => {
                                    return _serde::export::Err(__err);
                                }
                            }
                        }
                    };
                    let __field9 = match __field9 {
                        _serde::export::Some(__field9) => __field9,
                        _serde::export::None => {
                            match _serde::private::de::missing_field("elections") {
                                _serde::export::Ok(__val) => __val,
                                _serde::export::Err(__err) => {
                                    return _serde::export::Err(__err);
                                }
                            }
                        }
                    };
                    let __field10 = match __field10 {
                        _serde::export::Some(__field10) => __field10,
                        _serde::export::None => {
                            match _serde::private::de::missing_field("membershipInstance1") {
                                _serde::export::Ok(__val) => __val,
                                _serde::export::Err(__err) => {
                                    return _serde::export::Err(__err);
                                }
                            }
                        }
                    };
                    let __field11 = match __field11 {
                        _serde::export::Some(__field11) => __field11,
                        _serde::export::None => match _serde::private::de::missing_field("grandpa")
                        {
                            _serde::export::Ok(__val) => __val,
                            _serde::export::Err(__err) => {
                                return _serde::export::Err(__err);
                            }
                        },
                    };
                    let __field12 = match __field12 {
                        _serde::export::Some(__field12) => __field12,
                        _serde::export::None => {
                            match _serde::private::de::missing_field("contracts") {
                                _serde::export::Ok(__val) => __val,
                                _serde::export::Err(__err) => {
                                    return _serde::export::Err(__err);
                                }
                            }
                        }
                    };
                    let __field13 = match __field13 {
                        _serde::export::Some(__field13) => __field13,
                        _serde::export::None => match _serde::private::de::missing_field("sudo") {
                            _serde::export::Ok(__val) => __val,
                            _serde::export::Err(__err) => {
                                return _serde::export::Err(__err);
                            }
                        },
                    };
                    let __field14 = match __field14 {
                        _serde::export::Some(__field14) => __field14,
                        _serde::export::None => {
                            match _serde::private::de::missing_field("imOnline") {
                                _serde::export::Ok(__val) => __val,
                                _serde::export::Err(__err) => {
                                    return _serde::export::Err(__err);
                                }
                            }
                        }
                    };
                    let __field15 = match __field15 {
                        _serde::export::Some(__field15) => __field15,
                        _serde::export::None => {
                            match _serde::private::de::missing_field("authorityDiscovery") {
                                _serde::export::Ok(__val) => __val,
                                _serde::export::Err(__err) => {
                                    return _serde::export::Err(__err);
                                }
                            }
                        }
                    };
                    _serde::export::Ok(GenesisConfig {
                        system: __field0,
                        babe: __field1,
                        indices: __field2,
                        balances: __field3,
                        staking: __field4,
                        session: __field5,
                        democracy: __field6,
                        collective_Instance1: __field7,
                        collective_Instance2: __field8,
                        elections: __field9,
                        membership_Instance1: __field10,
                        grandpa: __field11,
                        contracts: __field12,
                        sudo: __field13,
                        im_online: __field14,
                        authority_discovery: __field15,
                    })
                }
            }
            const FIELDS: &'static [&'static str] = &[
                "system",
                "babe",
                "indices",
                "balances",
                "staking",
                "session",
                "democracy",
                "collectiveInstance1",
                "collectiveInstance2",
                "elections",
                "membershipInstance1",
                "grandpa",
                "contracts",
                "sudo",
                "imOnline",
                "authorityDiscovery",
            ];
            _serde::Deserializer::deserialize_struct(
                __deserializer,
                "GenesisConfig",
                FIELDS,
                __Visitor {
                    marker: _serde::export::PhantomData::<GenesisConfig>,
                    lifetime: _serde::export::PhantomData,
                },
            )
        }
    }
};
#[cfg(any(feature = "std", test))]
impl ::sr_primitives::BuildStorage for GenesisConfig {
    fn assimilate_storage(
        self,
        storage: &mut (
            ::sr_primitives::StorageOverlay,
            ::sr_primitives::ChildrenStorageOverlay,
        ),
    ) -> std::result::Result<(), String> {
        if let Some(extra) = self.system {
            :: sr_primitives :: BuildModuleGenesisStorage :: < Runtime , system :: __InherentHiddenInstance > :: build_module_genesis_storage ( extra , storage ) ? ;
        }
        if let Some(extra) = self.babe {
            :: sr_primitives :: BuildModuleGenesisStorage :: < Runtime , babe :: __InherentHiddenInstance > :: build_module_genesis_storage ( extra , storage ) ? ;
        }
        if let Some(extra) = self.indices {
            :: sr_primitives :: BuildModuleGenesisStorage :: < Runtime , indices :: __InherentHiddenInstance > :: build_module_genesis_storage ( extra , storage ) ? ;
        }
        if let Some(extra) = self.balances {
            ::sr_primitives::BuildModuleGenesisStorage::<
                Runtime,
                balances::__InherentHiddenInstance,
            >::build_module_genesis_storage(extra, storage)?;
        }
        if let Some(extra) = self.staking {
            :: sr_primitives :: BuildModuleGenesisStorage :: < Runtime , staking :: __InherentHiddenInstance > :: build_module_genesis_storage ( extra , storage ) ? ;
        }
        if let Some(extra) = self.session {
            :: sr_primitives :: BuildModuleGenesisStorage :: < Runtime , session :: __InherentHiddenInstance > :: build_module_genesis_storage ( extra , storage ) ? ;
        }
        if let Some(extra) = self.democracy {
            ::sr_primitives::BuildModuleGenesisStorage::<
                Runtime,
                democracy::__InherentHiddenInstance,
            >::build_module_genesis_storage(extra, storage)?;
        }
        if let Some(extra) = self.collective_Instance1 {
            :: sr_primitives :: BuildModuleGenesisStorage :: < Runtime , collective :: Instance1 > :: build_module_genesis_storage ( extra , storage ) ? ;
        }
        if let Some(extra) = self.collective_Instance2 {
            :: sr_primitives :: BuildModuleGenesisStorage :: < Runtime , collective :: Instance2 > :: build_module_genesis_storage ( extra , storage ) ? ;
        }
        if let Some(extra) = self.elections {
            ::sr_primitives::BuildModuleGenesisStorage::<
                Runtime,
                elections::__InherentHiddenInstance,
            >::build_module_genesis_storage(extra, storage)?;
        }
        if let Some(extra) = self.membership_Instance1 {
            :: sr_primitives :: BuildModuleGenesisStorage :: < Runtime , membership :: Instance1 > :: build_module_genesis_storage ( extra , storage ) ? ;
        }
        if let Some(extra) = self.grandpa {
            :: sr_primitives :: BuildModuleGenesisStorage :: < Runtime , grandpa :: __InherentHiddenInstance > :: build_module_genesis_storage ( extra , storage ) ? ;
        }
        if let Some(extra) = self.contracts {
            ::sr_primitives::BuildModuleGenesisStorage::<
                Runtime,
                contracts::__InherentHiddenInstance,
            >::build_module_genesis_storage(extra, storage)?;
        }
        if let Some(extra) = self.sudo {
            :: sr_primitives :: BuildModuleGenesisStorage :: < Runtime , sudo :: __InherentHiddenInstance > :: build_module_genesis_storage ( extra , storage ) ? ;
        }
        if let Some(extra) = self.im_online {
            ::sr_primitives::BuildModuleGenesisStorage::<
                Runtime,
                im_online::__InherentHiddenInstance,
            >::build_module_genesis_storage(extra, storage)?;
        }
        if let Some(extra) = self.authority_discovery {
            ::sr_primitives::BuildModuleGenesisStorage::<
                Runtime,
                authority_discovery::__InherentHiddenInstance,
            >::build_module_genesis_storage(extra, storage)?;
        }
        Ok(())
    }
}
trait InherentDataExt {
    fn create_extrinsics(
        &self,
    ) -> ::srml_support::inherent::Vec<<Block as ::srml_support::inherent::BlockT>::Extrinsic>;
    fn check_extrinsics(&self, block: &Block) -> ::srml_support::inherent::CheckInherentsResult;
}
impl InherentDataExt for ::srml_support::inherent::InherentData {
    fn create_extrinsics(
        &self,
    ) -> ::srml_support::inherent::Vec<<Block as ::srml_support::inherent::BlockT>::Extrinsic> {
        use srml_support::inherent::Extrinsic;
        use srml_support::inherent::ProvideInherent;
        let mut inherents = Vec::new();
        if let Some(inherent) = Babe::create_inherent(self) {
            inherents.push(
                UncheckedExtrinsic::new(Call::Timestamp(inherent), None).expect(
                    "Runtime UncheckedExtrinsic is not Opaque, so it has to return `Some`; qed",
                ),
            );
        }
        if let Some(inherent) = Timestamp::create_inherent(self) {
            inherents.push(
                UncheckedExtrinsic::new(Call::Timestamp(inherent), None).expect(
                    "Runtime UncheckedExtrinsic is not Opaque, so it has to return `Some`; qed",
                ),
            );
        }
        if let Some(inherent) = Authorship::create_inherent(self) {
            inherents.push(
                UncheckedExtrinsic::new(Call::Authorship(inherent), None).expect(
                    "Runtime UncheckedExtrinsic is not Opaque, so it has to return `Some`; qed",
                ),
            );
        }
        if let Some(inherent) = FinalityTracker::create_inherent(self) {
            inherents.push(
                UncheckedExtrinsic::new(Call::FinalityTracker(inherent), None).expect(
                    "Runtime UncheckedExtrinsic is not Opaque, so it has to return `Some`; qed",
                ),
            );
        }
        inherents
    }
    fn check_extrinsics(&self, block: &Block) -> ::srml_support::inherent::CheckInherentsResult {
        use srml_support::inherent::{IsFatalError, ProvideInherent};
        let mut result = ::srml_support::inherent::CheckInherentsResult::new();
        for xt in block.extrinsics() {
            if ::srml_support::inherent::Extrinsic::is_signed(xt).unwrap_or(false) {
                break;
            }
            match xt.function {
                Call::Timestamp(ref call) => {
                    if let Err(e) = Babe::check_inherent(call, self) {
                        result
                            .put_error(Babe::INHERENT_IDENTIFIER, &e)
                            .expect("There is only one fatal error; qed");
                        if e.is_fatal_error() {
                            return result;
                        }
                    }
                }
                _ => {}
            }
            match xt.function {
                Call::Timestamp(ref call) => {
                    if let Err(e) = Timestamp::check_inherent(call, self) {
                        result
                            .put_error(Timestamp::INHERENT_IDENTIFIER, &e)
                            .expect("There is only one fatal error; qed");
                        if e.is_fatal_error() {
                            return result;
                        }
                    }
                }
                _ => {}
            }
            match xt.function {
                Call::Authorship(ref call) => {
                    if let Err(e) = Authorship::check_inherent(call, self) {
                        result
                            .put_error(Authorship::INHERENT_IDENTIFIER, &e)
                            .expect("There is only one fatal error; qed");
                        if e.is_fatal_error() {
                            return result;
                        }
                    }
                }
                _ => {}
            }
            match xt.function {
                Call::FinalityTracker(ref call) => {
                    if let Err(e) = FinalityTracker::check_inherent(call, self) {
                        result
                            .put_error(FinalityTracker::INHERENT_IDENTIFIER, &e)
                            .expect("There is only one fatal error; qed");
                        if e.is_fatal_error() {
                            return result;
                        }
                    }
                }
                _ => {}
            }
        }
        result
    }
}
impl ::srml_support::unsigned::ValidateUnsigned for Runtime {
    type Call = Call;
    fn validate_unsigned(call: &Self::Call) -> ::srml_support::unsigned::TransactionValidity {
        #[allow(unreachable_patterns)]
        match call {
            Call::ImOnline(inner_call) => ImOnline::validate_unsigned(inner_call),
            _ => ::srml_support::unsigned::UnknownTransaction::NoUnsignedValidator.into(),
        }
    }
}
