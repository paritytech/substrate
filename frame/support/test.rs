pub mod interface {
    use crate::{
        dispatch::{CallMetadata, DispatchInfo, DispatchResultWithPostInfo, PostDispatchInfo},
        traits::{EnqueueMessage, GetCallMetadata, UnfilteredDispatchable},
    };
    use codec::{Decode, Encode};
    use frame_support::dispatch::DispatchErrorWithPostInfo;
    use sp_core::H256;
    use sp_runtime::{
        traits,
        traits::{Dispatchable, Zero},
        DispatchError, DispatchResultWithInfo, InterfaceError, ModuleError,
        MAX_MODULE_ERROR_ENCODED_SIZE,
    };
    #[doc(hidden)]
    mod sp_api_hidden_includes_DECL_RUNTIME_APIS {
        pub extern crate sp_api as sp_api;
    }
    #[doc(hidden)]
    #[allow(dead_code)]
    #[allow(deprecated)]
    pub mod runtime_decl_for_Interface {
        use super::*;
        pub trait InterfaceV1<
            Block: self::sp_api_hidden_includes_DECL_RUNTIME_APIS::sp_api::BlockT,
            View,
        >
        where
            View: sp_api::Encode + frame_support::interface::View,
        {
            fn view(
                view: frame_support::interface::InterfaceViewEntry<View>,
            ) -> Result<Vec<u8>, DispatchError>;
        }
        pub use InterfaceV1 as Interface;
        pub const VERSION: u32 = 1u32;
        pub const ID: [u8; 8] = [49u8, 166u8, 79u8, 11u8, 127u8, 47u8, 75u8, 143u8];
    }
    #[cfg(any(feature = "std", test))]
    pub trait Interface<Block: self::sp_api_hidden_includes_DECL_RUNTIME_APIS::sp_api::BlockT, View>:
        self::sp_api_hidden_includes_DECL_RUNTIME_APIS::sp_api::Core<Block>
    where
        View: sp_api::Encode + frame_support::interface::View,
    {
        fn view(
            &self,
            __runtime_api_at_param__ : < Block as self :: sp_api_hidden_includes_DECL_RUNTIME_APIS :: sp_api :: BlockT > :: Hash,
            view: frame_support::interface::InterfaceViewEntry<View>,
        ) -> std::result::Result<
            Result<Vec<u8>, DispatchError>,
            self::sp_api_hidden_includes_DECL_RUNTIME_APIS::sp_api::ApiError,
        > {
            let __runtime_api_impl_params_encoded__ =
                self::sp_api_hidden_includes_DECL_RUNTIME_APIS::sp_api::Encode::encode(&(&view));
            < Self as Interface < _ , _ > > :: __runtime_api_internal_call_api_at (self , __runtime_api_at_param__ , self :: sp_api_hidden_includes_DECL_RUNTIME_APIS :: sp_api :: ExecutionContext :: OffchainCall (None) , __runtime_api_impl_params_encoded__ , & (| version | { "Interface_view" })) . and_then (| r | std :: result :: Result :: map_err (< Result < Vec < u8 > , DispatchError > as self :: sp_api_hidden_includes_DECL_RUNTIME_APIS :: sp_api :: Decode > :: decode (& mut & r [..]) , | err | self :: sp_api_hidden_includes_DECL_RUNTIME_APIS :: sp_api :: ApiError :: FailedToDecodeReturnValue { function : "Interface_view" , error : err , }))
        }
        fn view_with_context(
            &self,
            __runtime_api_at_param__ : < Block as self :: sp_api_hidden_includes_DECL_RUNTIME_APIS :: sp_api :: BlockT > :: Hash,
            context: self::sp_api_hidden_includes_DECL_RUNTIME_APIS::sp_api::ExecutionContext,
            view: frame_support::interface::InterfaceViewEntry<View>,
        ) -> std::result::Result<
            Result<Vec<u8>, DispatchError>,
            self::sp_api_hidden_includes_DECL_RUNTIME_APIS::sp_api::ApiError,
        > {
            let __runtime_api_impl_params_encoded__ =
                self::sp_api_hidden_includes_DECL_RUNTIME_APIS::sp_api::Encode::encode(&(&view));
            < Self as Interface < _ , _ > > :: __runtime_api_internal_call_api_at (self , __runtime_api_at_param__ , context , __runtime_api_impl_params_encoded__ , & (| version | { "Interface_view" })) . and_then (| r | std :: result :: Result :: map_err (< Result < Vec < u8 > , DispatchError > as self :: sp_api_hidden_includes_DECL_RUNTIME_APIS :: sp_api :: Decode > :: decode (& mut & r [..]) , | err | self :: sp_api_hidden_includes_DECL_RUNTIME_APIS :: sp_api :: ApiError :: FailedToDecodeReturnValue { function : "Interface_view" , error : err , }))
        }
        /// !!INTERNAL USE ONLY!!
        #[doc(hidden)]
        fn __runtime_api_internal_call_api_at(
            &self,
            at: <Block as self::sp_api_hidden_includes_DECL_RUNTIME_APIS::sp_api::BlockT>::Hash,
            context: self::sp_api_hidden_includes_DECL_RUNTIME_APIS::sp_api::ExecutionContext,
            params: std::vec::Vec<u8>,
            fn_name: &dyn Fn(
                self::sp_api_hidden_includes_DECL_RUNTIME_APIS::sp_api::RuntimeVersion,
            ) -> &'static str,
        ) -> std::result::Result<
            std::vec::Vec<u8>,
            self::sp_api_hidden_includes_DECL_RUNTIME_APIS::sp_api::ApiError,
        >;
    }
    #[cfg(any(feature = "std", test))]
    impl<Block: self::sp_api_hidden_includes_DECL_RUNTIME_APIS::sp_api::BlockT, View>
        self::sp_api_hidden_includes_DECL_RUNTIME_APIS::sp_api::RuntimeApiInfo
        for dyn Interface<Block, View>
    {
        const ID: [u8; 8] = [49u8, 166u8, 79u8, 11u8, 127u8, 47u8, 75u8, 143u8];
        const VERSION: u32 = 1u32;
    }
    /// The result a call method of an interface must have
    pub type CallResult = Result<PostDispatchInfo, DispatchErrorWithPostInfo>;
    /// The result a view method of an interface must have
    pub type ViewResult<T> = Result<T, DispatchError>;
    /// The result a selector method of an interface must have
    pub type SelectorResult<T> = Result<SelectorResultWithInfo<T>, DispatchErrorWithPostInfo>;
    /// A helper struct that provides easy conversions
    ///
    /// I.e. it allows somebody who does not care about
    ///      the `PostDispatchInfo` in a selector method
    ///      to just call `Ok(T.into())` instead of
    ///      Ok((T, ().into())) if we used a tuple.
    pub struct SelectorResultWithInfo<T> {
        res: T,
        info: PostDispatchInfo,
    }
    impl<T> From<T> for SelectorResultWithInfo<T> {
        fn from(value: T) -> Self {
            SelectorResultWithInfo {
                res: value,
                info: Default::default(),
            }
        }
    }
    impl<T> From<(T, PostDispatchInfo)> for SelectorResultWithInfo<T> {
        fn from(value: (T, PostDispatchInfo)) -> Self {
            SelectorResultWithInfo {
                res: value.0,
                info: value.1,
            }
        }
    }
    impl<T> SelectorResultWithInfo<T> {
        /// Consumes self and returns the
        /// inner T
        pub fn result(self) -> T {
            self.res
        }
        /// Provides a copy of the inner
        /// `PostDispatchInfo`
        pub fn info(&self) -> PostDispatchInfo {
            self.info
        }
        /// Destructs self into a tuple of `(T, PostDispatchInfo)`
        pub fn destruct(self) -> (T, PostDispatchInfo) {
            (self.res, self.info)
        }
    }
    pub trait Core: 'static + Eq + Clone {
        type RuntimeOrigin;
    }
    pub trait Call {
        type RuntimeOrigin;
        fn call(self, origin: Self::RuntimeOrigin, selectable: H256) -> CallResult;
    }
    pub trait View {
        fn view(self, selectable: H256) -> Result<Vec<u8>, DispatchError>;
    }
    pub trait Selector {
        type Selected;
        fn select(&self, selectable: H256) -> SelectorResult<Self::Selected>;
    }
    pub struct InterfaceCallEntry<CallInterface> {
        selectable: H256,
        interface: CallInterface,
    }
    #[doc(hidden)]
    #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
    const _: () = {
        #[allow(unused_extern_crates, clippy::useless_attribute)]
        extern crate serde as _serde;
        #[automatically_derived]
        impl<CallInterface> _serde::Serialize for InterfaceCallEntry<CallInterface>
        where
            CallInterface: _serde::Serialize,
        {
            fn serialize<__S>(
                &self,
                __serializer: __S,
            ) -> _serde::__private::Result<__S::Ok, __S::Error>
            where
                __S: _serde::Serializer,
            {
                let mut __serde_state = match _serde::Serializer::serialize_struct(
                    __serializer,
                    "InterfaceCallEntry",
                    false as usize + 1 + 1,
                ) {
                    _serde::__private::Ok(__val) => __val,
                    _serde::__private::Err(__err) => {
                        return _serde::__private::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(
                    &mut __serde_state,
                    "selectable",
                    &self.selectable,
                ) {
                    _serde::__private::Ok(__val) => __val,
                    _serde::__private::Err(__err) => {
                        return _serde::__private::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(
                    &mut __serde_state,
                    "interface",
                    &self.interface,
                ) {
                    _serde::__private::Ok(__val) => __val,
                    _serde::__private::Err(__err) => {
                        return _serde::__private::Err(__err);
                    }
                };
                _serde::ser::SerializeStruct::end(__serde_state)
            }
        }
    };
    #[doc(hidden)]
    #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
    const _: () = {
        #[allow(unused_extern_crates, clippy::useless_attribute)]
        extern crate serde as _serde;
        #[automatically_derived]
        impl<'de, CallInterface> _serde::Deserialize<'de> for InterfaceCallEntry<CallInterface>
        where
            CallInterface: _serde::Deserialize<'de>,
        {
            fn deserialize<__D>(__deserializer: __D) -> _serde::__private::Result<Self, __D::Error>
            where
                __D: _serde::Deserializer<'de>,
            {
                #[allow(non_camel_case_types)]
                enum __Field {
                    __field0,
                    __field1,
                    __ignore,
                }
                struct __FieldVisitor;
                impl<'de> _serde::de::Visitor<'de> for __FieldVisitor {
                    type Value = __Field;
                    fn expecting(
                        &self,
                        __formatter: &mut _serde::__private::Formatter,
                    ) -> _serde::__private::fmt::Result {
                        _serde::__private::Formatter::write_str(__formatter, "field identifier")
                    }
                    fn visit_u64<__E>(
                        self,
                        __value: u64,
                    ) -> _serde::__private::Result<Self::Value, __E>
                    where
                        __E: _serde::de::Error,
                    {
                        match __value {
                            0u64 => _serde::__private::Ok(__Field::__field0),
                            1u64 => _serde::__private::Ok(__Field::__field1),
                            _ => _serde::__private::Ok(__Field::__ignore),
                        }
                    }
                    fn visit_str<__E>(
                        self,
                        __value: &str,
                    ) -> _serde::__private::Result<Self::Value, __E>
                    where
                        __E: _serde::de::Error,
                    {
                        match __value {
                            "selectable" => _serde::__private::Ok(__Field::__field0),
                            "interface" => _serde::__private::Ok(__Field::__field1),
                            _ => _serde::__private::Ok(__Field::__ignore),
                        }
                    }
                    fn visit_bytes<__E>(
                        self,
                        __value: &[u8],
                    ) -> _serde::__private::Result<Self::Value, __E>
                    where
                        __E: _serde::de::Error,
                    {
                        match __value {
                            b"selectable" => _serde::__private::Ok(__Field::__field0),
                            b"interface" => _serde::__private::Ok(__Field::__field1),
                            _ => _serde::__private::Ok(__Field::__ignore),
                        }
                    }
                }
                impl<'de> _serde::Deserialize<'de> for __Field {
                    #[inline]
                    fn deserialize<__D>(
                        __deserializer: __D,
                    ) -> _serde::__private::Result<Self, __D::Error>
                    where
                        __D: _serde::Deserializer<'de>,
                    {
                        _serde::Deserializer::deserialize_identifier(__deserializer, __FieldVisitor)
                    }
                }
                struct __Visitor<'de, CallInterface>
                where
                    CallInterface: _serde::Deserialize<'de>,
                {
                    marker: _serde::__private::PhantomData<InterfaceCallEntry<CallInterface>>,
                    lifetime: _serde::__private::PhantomData<&'de ()>,
                }
                impl<'de, CallInterface> _serde::de::Visitor<'de> for __Visitor<'de, CallInterface>
                where
                    CallInterface: _serde::Deserialize<'de>,
                {
                    type Value = InterfaceCallEntry<CallInterface>;
                    fn expecting(
                        &self,
                        __formatter: &mut _serde::__private::Formatter,
                    ) -> _serde::__private::fmt::Result {
                        _serde::__private::Formatter::write_str(
                            __formatter,
                            "struct InterfaceCallEntry",
                        )
                    }
                    #[inline]
                    fn visit_seq<__A>(
                        self,
                        mut __seq: __A,
                    ) -> _serde::__private::Result<Self::Value, __A::Error>
                    where
                        __A: _serde::de::SeqAccess<'de>,
                    {
                        let __field0 =
                            match match _serde::de::SeqAccess::next_element::<H256>(&mut __seq) {
                                _serde::__private::Ok(__val) => __val,
                                _serde::__private::Err(__err) => {
                                    return _serde::__private::Err(__err);
                                }
                            } {
                                _serde::__private::Some(__value) => __value,
                                _serde::__private::None => {
                                    return _serde::__private::Err(
                                        _serde::de::Error::invalid_length(
                                            0usize,
                                            &"struct InterfaceCallEntry with 2 elements",
                                        ),
                                    );
                                }
                            };
                        let __field1 = match match _serde::de::SeqAccess::next_element::<
                            CallInterface,
                        >(&mut __seq)
                        {
                            _serde::__private::Ok(__val) => __val,
                            _serde::__private::Err(__err) => {
                                return _serde::__private::Err(__err);
                            }
                        } {
                            _serde::__private::Some(__value) => __value,
                            _serde::__private::None => {
                                return _serde::__private::Err(_serde::de::Error::invalid_length(
                                    1usize,
                                    &"struct InterfaceCallEntry with 2 elements",
                                ));
                            }
                        };
                        _serde::__private::Ok(InterfaceCallEntry {
                            selectable: __field0,
                            interface: __field1,
                        })
                    }
                    #[inline]
                    fn visit_map<__A>(
                        self,
                        mut __map: __A,
                    ) -> _serde::__private::Result<Self::Value, __A::Error>
                    where
                        __A: _serde::de::MapAccess<'de>,
                    {
                        let mut __field0: _serde::__private::Option<H256> = _serde::__private::None;
                        let mut __field1: _serde::__private::Option<CallInterface> =
                            _serde::__private::None;
                        while let _serde::__private::Some(__key) =
                            match _serde::de::MapAccess::next_key::<__Field>(&mut __map) {
                                _serde::__private::Ok(__val) => __val,
                                _serde::__private::Err(__err) => {
                                    return _serde::__private::Err(__err);
                                }
                            }
                        {
                            match __key {
                                __Field::__field0 => {
                                    if _serde::__private::Option::is_some(&__field0) {
                                        return _serde::__private::Err(
                                            <__A::Error as _serde::de::Error>::duplicate_field(
                                                "selectable",
                                            ),
                                        );
                                    }
                                    __field0 = _serde::__private::Some(
                                        match _serde::de::MapAccess::next_value::<H256>(&mut __map)
                                        {
                                            _serde::__private::Ok(__val) => __val,
                                            _serde::__private::Err(__err) => {
                                                return _serde::__private::Err(__err);
                                            }
                                        },
                                    );
                                }
                                __Field::__field1 => {
                                    if _serde::__private::Option::is_some(&__field1) {
                                        return _serde::__private::Err(
                                            <__A::Error as _serde::de::Error>::duplicate_field(
                                                "interface",
                                            ),
                                        );
                                    }
                                    __field1 = _serde::__private::Some(
                                        match _serde::de::MapAccess::next_value::<CallInterface>(
                                            &mut __map,
                                        ) {
                                            _serde::__private::Ok(__val) => __val,
                                            _serde::__private::Err(__err) => {
                                                return _serde::__private::Err(__err);
                                            }
                                        },
                                    );
                                }
                                _ => {
                                    let _ = match _serde::de::MapAccess::next_value::<
                                        _serde::de::IgnoredAny,
                                    >(&mut __map)
                                    {
                                        _serde::__private::Ok(__val) => __val,
                                        _serde::__private::Err(__err) => {
                                            return _serde::__private::Err(__err);
                                        }
                                    };
                                }
                            }
                        }
                        let __field0 = match __field0 {
                            _serde::__private::Some(__field0) => __field0,
                            _serde::__private::None => {
                                match _serde::__private::de::missing_field("selectable") {
                                    _serde::__private::Ok(__val) => __val,
                                    _serde::__private::Err(__err) => {
                                        return _serde::__private::Err(__err);
                                    }
                                }
                            }
                        };
                        let __field1 = match __field1 {
                            _serde::__private::Some(__field1) => __field1,
                            _serde::__private::None => {
                                match _serde::__private::de::missing_field("interface") {
                                    _serde::__private::Ok(__val) => __val,
                                    _serde::__private::Err(__err) => {
                                        return _serde::__private::Err(__err);
                                    }
                                }
                            }
                        };
                        _serde::__private::Ok(InterfaceCallEntry {
                            selectable: __field0,
                            interface: __field1,
                        })
                    }
                }
                const FIELDS: &'static [&'static str] = &["selectable", "interface"];
                _serde::Deserializer::deserialize_struct(
                    __deserializer,
                    "InterfaceCallEntry",
                    FIELDS,
                    __Visitor {
                        marker: _serde::__private::PhantomData::<InterfaceCallEntry<CallInterface>>,
                        lifetime: _serde::__private::PhantomData,
                    },
                )
            }
        }
    };
    #[automatically_derived]
    impl<CallInterface> ::core::marker::StructuralPartialEq for InterfaceCallEntry<CallInterface> {}
    #[automatically_derived]
    impl<CallInterface: ::core::cmp::PartialEq> ::core::cmp::PartialEq
        for InterfaceCallEntry<CallInterface>
    {
        #[inline]
        fn eq(&self, other: &InterfaceCallEntry<CallInterface>) -> bool {
            self.selectable == other.selectable && self.interface == other.interface
        }
    }
    #[automatically_derived]
    impl<CallInterface> ::core::marker::StructuralEq for InterfaceCallEntry<CallInterface> {}
    #[automatically_derived]
    impl<CallInterface: ::core::cmp::Eq> ::core::cmp::Eq for InterfaceCallEntry<CallInterface> {
        #[inline]
        #[doc(hidden)]
        #[no_coverage]
        fn assert_receiver_is_total_eq(&self) -> () {
            let _: ::core::cmp::AssertParamIsEq<H256>;
            let _: ::core::cmp::AssertParamIsEq<CallInterface>;
        }
    }
    #[automatically_derived]
    impl<CallInterface: ::core::clone::Clone> ::core::clone::Clone
        for InterfaceCallEntry<CallInterface>
    {
        #[inline]
        fn clone(&self) -> InterfaceCallEntry<CallInterface> {
            InterfaceCallEntry {
                selectable: ::core::clone::Clone::clone(&self.selectable),
                interface: ::core::clone::Clone::clone(&self.interface),
            }
        }
    }
    #[automatically_derived]
    impl<CallInterface: ::core::marker::Copy> ::core::marker::Copy
        for InterfaceCallEntry<CallInterface>
    {
    }
    #[allow(deprecated)]
    const _: () = {
        #[automatically_derived]
        impl<CallInterface> ::codec::Encode for InterfaceCallEntry<CallInterface>
        where
            CallInterface: ::codec::Encode,
            CallInterface: ::codec::Encode,
        {
            fn encode_to<__CodecOutputEdqy: ::codec::Output + ?::core::marker::Sized>(
                &self,
                __codec_dest_edqy: &mut __CodecOutputEdqy,
            ) {
                ::codec::Encode::encode_to(&self.selectable, __codec_dest_edqy);
                ::codec::Encode::encode_to(&self.interface, __codec_dest_edqy);
            }
        }
        #[automatically_derived]
        impl<CallInterface> ::codec::EncodeLike for InterfaceCallEntry<CallInterface>
        where
            CallInterface: ::codec::Encode,
            CallInterface: ::codec::Encode,
        {
        }
    };
    #[allow(deprecated)]
    const _: () = {
        #[automatically_derived]
        impl<CallInterface> ::codec::Decode for InterfaceCallEntry<CallInterface>
        where
            CallInterface: ::codec::Decode,
            CallInterface: ::codec::Decode,
        {
            fn decode<__CodecInputEdqy: ::codec::Input>(
                __codec_input_edqy: &mut __CodecInputEdqy,
            ) -> ::core::result::Result<Self, ::codec::Error> {
                ::core::result::Result::Ok(InterfaceCallEntry::<CallInterface> {
                    selectable: {
                        let __codec_res_edqy =
                            <H256 as ::codec::Decode>::decode(__codec_input_edqy);
                        match __codec_res_edqy {
                            ::core::result::Result::Err(e) => {
                                return ::core::result::Result::Err(
                                    e.chain("Could not decode `InterfaceCallEntry::selectable`"),
                                )
                            }
                            ::core::result::Result::Ok(__codec_res_edqy) => __codec_res_edqy,
                        }
                    },
                    interface: {
                        let __codec_res_edqy =
                            <CallInterface as ::codec::Decode>::decode(__codec_input_edqy);
                        match __codec_res_edqy {
                            ::core::result::Result::Err(e) => {
                                return ::core::result::Result::Err(
                                    e.chain("Could not decode `InterfaceCallEntry::interface`"),
                                )
                            }
                            ::core::result::Result::Ok(__codec_res_edqy) => __codec_res_edqy,
                        }
                    },
                })
            }
        }
    };
    #[automatically_derived]
    impl<CallInterface: ::core::fmt::Debug> ::core::fmt::Debug for InterfaceCallEntry<CallInterface> {
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(
                f,
                "InterfaceCallEntry",
                "selectable",
                &self.selectable,
                "interface",
                &&self.interface,
            )
        }
    }
    #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
    const _: () = {
        impl<CallInterface> ::scale_info::TypeInfo for InterfaceCallEntry<CallInterface>
        where
            CallInterface: ::scale_info::TypeInfo + 'static,
            CallInterface: ::scale_info::TypeInfo + 'static,
        {
            type Identity = Self;
            fn type_info() -> ::scale_info::Type {
                :: scale_info :: Type :: builder () . path (:: scale_info :: Path :: new ("InterfaceCallEntry" , "frame_support::interface")) . type_params (< [_] > :: into_vec (# [rustc_box] :: alloc :: boxed :: Box :: new ([:: scale_info :: TypeParameter :: new ("CallInterface" , :: core :: option :: Option :: Some (:: scale_info :: meta_type :: < CallInterface > ()))]))) . composite (:: scale_info :: build :: Fields :: named () . field (| f | f . ty :: < H256 > () . name ("selectable") . type_name ("H256")) . field (| f | f . ty :: < CallInterface > () . name ("interface") . type_name ("CallInterface")))
            }
        };
    };
    const _: () = {
        impl<CallInterface> ::codec::MaxEncodedLen for InterfaceCallEntry<CallInterface>
        where
            CallInterface: ::codec::MaxEncodedLen,
            CallInterface: ::codec::MaxEncodedLen,
        {
            fn max_encoded_len() -> ::core::primitive::usize {
                0_usize
                    .saturating_add(<H256>::max_encoded_len())
                    .saturating_add(<CallInterface>::max_encoded_len())
            }
        }
    };
    impl<CallInterface> UnfilteredDispatchable for InterfaceCallEntry<CallInterface>
    where
        CallInterface: Call<RuntimeOrigin = <CallInterface as Core>::RuntimeOrigin> + Core,
    {
        type RuntimeOrigin = <CallInterface as Core>::RuntimeOrigin;
        fn dispatch_bypass_filter(self, origin: Self::RuntimeOrigin) -> DispatchResultWithPostInfo {
            self.interface.call(origin, self.selectable)
        }
    }
    pub struct InterfaceViewEntry<ViewInterface> {
        selectable: H256,
        interface: ViewInterface,
    }
    #[doc(hidden)]
    #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
    const _: () = {
        #[allow(unused_extern_crates, clippy::useless_attribute)]
        extern crate serde as _serde;
        #[automatically_derived]
        impl<ViewInterface> _serde::Serialize for InterfaceViewEntry<ViewInterface>
        where
            ViewInterface: _serde::Serialize,
        {
            fn serialize<__S>(
                &self,
                __serializer: __S,
            ) -> _serde::__private::Result<__S::Ok, __S::Error>
            where
                __S: _serde::Serializer,
            {
                let mut __serde_state = match _serde::Serializer::serialize_struct(
                    __serializer,
                    "InterfaceViewEntry",
                    false as usize + 1 + 1,
                ) {
                    _serde::__private::Ok(__val) => __val,
                    _serde::__private::Err(__err) => {
                        return _serde::__private::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(
                    &mut __serde_state,
                    "selectable",
                    &self.selectable,
                ) {
                    _serde::__private::Ok(__val) => __val,
                    _serde::__private::Err(__err) => {
                        return _serde::__private::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(
                    &mut __serde_state,
                    "interface",
                    &self.interface,
                ) {
                    _serde::__private::Ok(__val) => __val,
                    _serde::__private::Err(__err) => {
                        return _serde::__private::Err(__err);
                    }
                };
                _serde::ser::SerializeStruct::end(__serde_state)
            }
        }
    };
    #[doc(hidden)]
    #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
    const _: () = {
        #[allow(unused_extern_crates, clippy::useless_attribute)]
        extern crate serde as _serde;
        #[automatically_derived]
        impl<'de, ViewInterface> _serde::Deserialize<'de> for InterfaceViewEntry<ViewInterface>
        where
            ViewInterface: _serde::Deserialize<'de>,
        {
            fn deserialize<__D>(__deserializer: __D) -> _serde::__private::Result<Self, __D::Error>
            where
                __D: _serde::Deserializer<'de>,
            {
                #[allow(non_camel_case_types)]
                enum __Field {
                    __field0,
                    __field1,
                    __ignore,
                }
                struct __FieldVisitor;
                impl<'de> _serde::de::Visitor<'de> for __FieldVisitor {
                    type Value = __Field;
                    fn expecting(
                        &self,
                        __formatter: &mut _serde::__private::Formatter,
                    ) -> _serde::__private::fmt::Result {
                        _serde::__private::Formatter::write_str(__formatter, "field identifier")
                    }
                    fn visit_u64<__E>(
                        self,
                        __value: u64,
                    ) -> _serde::__private::Result<Self::Value, __E>
                    where
                        __E: _serde::de::Error,
                    {
                        match __value {
                            0u64 => _serde::__private::Ok(__Field::__field0),
                            1u64 => _serde::__private::Ok(__Field::__field1),
                            _ => _serde::__private::Ok(__Field::__ignore),
                        }
                    }
                    fn visit_str<__E>(
                        self,
                        __value: &str,
                    ) -> _serde::__private::Result<Self::Value, __E>
                    where
                        __E: _serde::de::Error,
                    {
                        match __value {
                            "selectable" => _serde::__private::Ok(__Field::__field0),
                            "interface" => _serde::__private::Ok(__Field::__field1),
                            _ => _serde::__private::Ok(__Field::__ignore),
                        }
                    }
                    fn visit_bytes<__E>(
                        self,
                        __value: &[u8],
                    ) -> _serde::__private::Result<Self::Value, __E>
                    where
                        __E: _serde::de::Error,
                    {
                        match __value {
                            b"selectable" => _serde::__private::Ok(__Field::__field0),
                            b"interface" => _serde::__private::Ok(__Field::__field1),
                            _ => _serde::__private::Ok(__Field::__ignore),
                        }
                    }
                }
                impl<'de> _serde::Deserialize<'de> for __Field {
                    #[inline]
                    fn deserialize<__D>(
                        __deserializer: __D,
                    ) -> _serde::__private::Result<Self, __D::Error>
                    where
                        __D: _serde::Deserializer<'de>,
                    {
                        _serde::Deserializer::deserialize_identifier(__deserializer, __FieldVisitor)
                    }
                }
                struct __Visitor<'de, ViewInterface>
                where
                    ViewInterface: _serde::Deserialize<'de>,
                {
                    marker: _serde::__private::PhantomData<InterfaceViewEntry<ViewInterface>>,
                    lifetime: _serde::__private::PhantomData<&'de ()>,
                }
                impl<'de, ViewInterface> _serde::de::Visitor<'de> for __Visitor<'de, ViewInterface>
                where
                    ViewInterface: _serde::Deserialize<'de>,
                {
                    type Value = InterfaceViewEntry<ViewInterface>;
                    fn expecting(
                        &self,
                        __formatter: &mut _serde::__private::Formatter,
                    ) -> _serde::__private::fmt::Result {
                        _serde::__private::Formatter::write_str(
                            __formatter,
                            "struct InterfaceViewEntry",
                        )
                    }
                    #[inline]
                    fn visit_seq<__A>(
                        self,
                        mut __seq: __A,
                    ) -> _serde::__private::Result<Self::Value, __A::Error>
                    where
                        __A: _serde::de::SeqAccess<'de>,
                    {
                        let __field0 =
                            match match _serde::de::SeqAccess::next_element::<H256>(&mut __seq) {
                                _serde::__private::Ok(__val) => __val,
                                _serde::__private::Err(__err) => {
                                    return _serde::__private::Err(__err);
                                }
                            } {
                                _serde::__private::Some(__value) => __value,
                                _serde::__private::None => {
                                    return _serde::__private::Err(
                                        _serde::de::Error::invalid_length(
                                            0usize,
                                            &"struct InterfaceViewEntry with 2 elements",
                                        ),
                                    );
                                }
                            };
                        let __field1 = match match _serde::de::SeqAccess::next_element::<
                            ViewInterface,
                        >(&mut __seq)
                        {
                            _serde::__private::Ok(__val) => __val,
                            _serde::__private::Err(__err) => {
                                return _serde::__private::Err(__err);
                            }
                        } {
                            _serde::__private::Some(__value) => __value,
                            _serde::__private::None => {
                                return _serde::__private::Err(_serde::de::Error::invalid_length(
                                    1usize,
                                    &"struct InterfaceViewEntry with 2 elements",
                                ));
                            }
                        };
                        _serde::__private::Ok(InterfaceViewEntry {
                            selectable: __field0,
                            interface: __field1,
                        })
                    }
                    #[inline]
                    fn visit_map<__A>(
                        self,
                        mut __map: __A,
                    ) -> _serde::__private::Result<Self::Value, __A::Error>
                    where
                        __A: _serde::de::MapAccess<'de>,
                    {
                        let mut __field0: _serde::__private::Option<H256> = _serde::__private::None;
                        let mut __field1: _serde::__private::Option<ViewInterface> =
                            _serde::__private::None;
                        while let _serde::__private::Some(__key) =
                            match _serde::de::MapAccess::next_key::<__Field>(&mut __map) {
                                _serde::__private::Ok(__val) => __val,
                                _serde::__private::Err(__err) => {
                                    return _serde::__private::Err(__err);
                                }
                            }
                        {
                            match __key {
                                __Field::__field0 => {
                                    if _serde::__private::Option::is_some(&__field0) {
                                        return _serde::__private::Err(
                                            <__A::Error as _serde::de::Error>::duplicate_field(
                                                "selectable",
                                            ),
                                        );
                                    }
                                    __field0 = _serde::__private::Some(
                                        match _serde::de::MapAccess::next_value::<H256>(&mut __map)
                                        {
                                            _serde::__private::Ok(__val) => __val,
                                            _serde::__private::Err(__err) => {
                                                return _serde::__private::Err(__err);
                                            }
                                        },
                                    );
                                }
                                __Field::__field1 => {
                                    if _serde::__private::Option::is_some(&__field1) {
                                        return _serde::__private::Err(
                                            <__A::Error as _serde::de::Error>::duplicate_field(
                                                "interface",
                                            ),
                                        );
                                    }
                                    __field1 = _serde::__private::Some(
                                        match _serde::de::MapAccess::next_value::<ViewInterface>(
                                            &mut __map,
                                        ) {
                                            _serde::__private::Ok(__val) => __val,
                                            _serde::__private::Err(__err) => {
                                                return _serde::__private::Err(__err);
                                            }
                                        },
                                    );
                                }
                                _ => {
                                    let _ = match _serde::de::MapAccess::next_value::<
                                        _serde::de::IgnoredAny,
                                    >(&mut __map)
                                    {
                                        _serde::__private::Ok(__val) => __val,
                                        _serde::__private::Err(__err) => {
                                            return _serde::__private::Err(__err);
                                        }
                                    };
                                }
                            }
                        }
                        let __field0 = match __field0 {
                            _serde::__private::Some(__field0) => __field0,
                            _serde::__private::None => {
                                match _serde::__private::de::missing_field("selectable") {
                                    _serde::__private::Ok(__val) => __val,
                                    _serde::__private::Err(__err) => {
                                        return _serde::__private::Err(__err);
                                    }
                                }
                            }
                        };
                        let __field1 = match __field1 {
                            _serde::__private::Some(__field1) => __field1,
                            _serde::__private::None => {
                                match _serde::__private::de::missing_field("interface") {
                                    _serde::__private::Ok(__val) => __val,
                                    _serde::__private::Err(__err) => {
                                        return _serde::__private::Err(__err);
                                    }
                                }
                            }
                        };
                        _serde::__private::Ok(InterfaceViewEntry {
                            selectable: __field0,
                            interface: __field1,
                        })
                    }
                }
                const FIELDS: &'static [&'static str] = &["selectable", "interface"];
                _serde::Deserializer::deserialize_struct(
                    __deserializer,
                    "InterfaceViewEntry",
                    FIELDS,
                    __Visitor {
                        marker: _serde::__private::PhantomData::<InterfaceViewEntry<ViewInterface>>,
                        lifetime: _serde::__private::PhantomData,
                    },
                )
            }
        }
    };
    #[automatically_derived]
    impl<ViewInterface> ::core::marker::StructuralPartialEq for InterfaceViewEntry<ViewInterface> {}
    #[automatically_derived]
    impl<ViewInterface: ::core::cmp::PartialEq> ::core::cmp::PartialEq
        for InterfaceViewEntry<ViewInterface>
    {
        #[inline]
        fn eq(&self, other: &InterfaceViewEntry<ViewInterface>) -> bool {
            self.selectable == other.selectable && self.interface == other.interface
        }
    }
    #[automatically_derived]
    impl<ViewInterface> ::core::marker::StructuralEq for InterfaceViewEntry<ViewInterface> {}
    #[automatically_derived]
    impl<ViewInterface: ::core::cmp::Eq> ::core::cmp::Eq for InterfaceViewEntry<ViewInterface> {
        #[inline]
        #[doc(hidden)]
        #[no_coverage]
        fn assert_receiver_is_total_eq(&self) -> () {
            let _: ::core::cmp::AssertParamIsEq<H256>;
            let _: ::core::cmp::AssertParamIsEq<ViewInterface>;
        }
    }
    #[automatically_derived]
    impl<ViewInterface: ::core::clone::Clone> ::core::clone::Clone
        for InterfaceViewEntry<ViewInterface>
    {
        #[inline]
        fn clone(&self) -> InterfaceViewEntry<ViewInterface> {
            InterfaceViewEntry {
                selectable: ::core::clone::Clone::clone(&self.selectable),
                interface: ::core::clone::Clone::clone(&self.interface),
            }
        }
    }
    #[automatically_derived]
    impl<ViewInterface: ::core::marker::Copy> ::core::marker::Copy
        for InterfaceViewEntry<ViewInterface>
    {
    }
    #[allow(deprecated)]
    const _: () = {
        #[automatically_derived]
        impl<ViewInterface> ::codec::Encode for InterfaceViewEntry<ViewInterface>
        where
            ViewInterface: ::codec::Encode,
            ViewInterface: ::codec::Encode,
        {
            fn encode_to<__CodecOutputEdqy: ::codec::Output + ?::core::marker::Sized>(
                &self,
                __codec_dest_edqy: &mut __CodecOutputEdqy,
            ) {
                ::codec::Encode::encode_to(&self.selectable, __codec_dest_edqy);
                ::codec::Encode::encode_to(&self.interface, __codec_dest_edqy);
            }
        }
        #[automatically_derived]
        impl<ViewInterface> ::codec::EncodeLike for InterfaceViewEntry<ViewInterface>
        where
            ViewInterface: ::codec::Encode,
            ViewInterface: ::codec::Encode,
        {
        }
    };
    #[allow(deprecated)]
    const _: () = {
        #[automatically_derived]
        impl<ViewInterface> ::codec::Decode for InterfaceViewEntry<ViewInterface>
        where
            ViewInterface: ::codec::Decode,
            ViewInterface: ::codec::Decode,
        {
            fn decode<__CodecInputEdqy: ::codec::Input>(
                __codec_input_edqy: &mut __CodecInputEdqy,
            ) -> ::core::result::Result<Self, ::codec::Error> {
                ::core::result::Result::Ok(InterfaceViewEntry::<ViewInterface> {
                    selectable: {
                        let __codec_res_edqy =
                            <H256 as ::codec::Decode>::decode(__codec_input_edqy);
                        match __codec_res_edqy {
                            ::core::result::Result::Err(e) => {
                                return ::core::result::Result::Err(
                                    e.chain("Could not decode `InterfaceViewEntry::selectable`"),
                                )
                            }
                            ::core::result::Result::Ok(__codec_res_edqy) => __codec_res_edqy,
                        }
                    },
                    interface: {
                        let __codec_res_edqy =
                            <ViewInterface as ::codec::Decode>::decode(__codec_input_edqy);
                        match __codec_res_edqy {
                            ::core::result::Result::Err(e) => {
                                return ::core::result::Result::Err(
                                    e.chain("Could not decode `InterfaceViewEntry::interface`"),
                                )
                            }
                            ::core::result::Result::Ok(__codec_res_edqy) => __codec_res_edqy,
                        }
                    },
                })
            }
        }
    };
    #[automatically_derived]
    impl<ViewInterface: ::core::fmt::Debug> ::core::fmt::Debug for InterfaceViewEntry<ViewInterface> {
        fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
            ::core::fmt::Formatter::debug_struct_field2_finish(
                f,
                "InterfaceViewEntry",
                "selectable",
                &self.selectable,
                "interface",
                &&self.interface,
            )
        }
    }
    #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
    const _: () = {
        impl<ViewInterface> ::scale_info::TypeInfo for InterfaceViewEntry<ViewInterface>
        where
            ViewInterface: ::scale_info::TypeInfo + 'static,
            ViewInterface: ::scale_info::TypeInfo + 'static,
        {
            type Identity = Self;
            fn type_info() -> ::scale_info::Type {
                :: scale_info :: Type :: builder () . path (:: scale_info :: Path :: new ("InterfaceViewEntry" , "frame_support::interface")) . type_params (< [_] > :: into_vec (# [rustc_box] :: alloc :: boxed :: Box :: new ([:: scale_info :: TypeParameter :: new ("ViewInterface" , :: core :: option :: Option :: Some (:: scale_info :: meta_type :: < ViewInterface > ()))]))) . composite (:: scale_info :: build :: Fields :: named () . field (| f | f . ty :: < H256 > () . name ("selectable") . type_name ("H256")) . field (| f | f . ty :: < ViewInterface > () . name ("interface") . type_name ("ViewInterface")))
            }
        };
    };
    const _: () = {
        impl<ViewInterface> ::codec::MaxEncodedLen for InterfaceViewEntry<ViewInterface>
        where
            ViewInterface: ::codec::MaxEncodedLen,
            ViewInterface: ::codec::MaxEncodedLen,
        {
            fn max_encoded_len() -> ::core::primitive::usize {
                0_usize
                    .saturating_add(<H256>::max_encoded_len())
                    .saturating_add(<ViewInterface>::max_encoded_len())
            }
        }
    };
    impl<ViewInterface> InterfaceViewEntry<ViewInterface>
    where
        ViewInterface: View,
    {
        pub fn view(self) -> Result<Vec<u8>, DispatchError> {
            self.interface.view(self.selectable)
        }
    }
    pub struct EmptySelector;
    impl EmptySelector {
        pub fn new() -> Self {
            EmptySelector {}
        }
    }
    impl Selector for EmptySelector {
        type Selected = ();
        fn select(&self, from: H256) -> SelectorResult<Self::Selected> {
            match from {
                x if x == H256::zero() => Ok(().into()),
                _ => Err(InterfaceError::ExpectedEmptySelectable.into()),
            }
        }
    }
    pub struct Select<T> {
        from: H256,
        selector: Box<dyn Selector<Selected = T>>,
    }
    impl<T> Select<T> {
        pub fn new(from: H256, selector: Box<dyn Selector<Selected = T>>) -> Self {
            Select { from, selector }
        }
        pub fn select(self) -> SelectorResult<T> {
            self.selector.as_ref().select(self.from)
        }
    }
    mod tests {
        mod int_123 {
            use crate::interface::{CallResult, ViewResult};
            use frame_support::{
                dispatch::DispatchResult,
                interface::{Select, SelectorResult},
                Parameter,
            };
            use sp_core::H256;
            use sp_runtime::traits::Member;
            pub trait Pip20: frame_support::interface::Core {
                type AccountId: Parameter + Member;
                type Currency: Parameter + Member;
                type Balance: Parameter + Member;
                fn select_currency(selectable: H256) -> SelectorResult<Self::Currency>;
                fn select_restricted_currency(selectable: H256) -> SelectorResult<Self::Currency>;
                fn select_account(selectable: H256) -> SelectorResult<Self::AccountId>;
                fn free_balance(
                    currency: Select<Self::Currency>,
                    who: Self::AccountId,
                ) -> ViewResult<Self::Currency>;
                fn balances(
                    who: Self::AccountId,
                ) -> ViewResult<Vec<(Self::Currency, Self::Balance)>>;
                fn transfer(
                    origin: Self::RuntimeOrigin,
                    currency: Select<Self::Currency>,
                    recv: Self::AccountId,
                    amount: Self::Balance,
                ) -> CallResult;
                fn burn(
                    origin: Self::RuntimeOrigin,
                    from: Self::AccountId,
                    amount: Self::Balance,
                ) -> CallResult;
                fn approve(
                    origin: Self::RuntimeOrigin,
                    currency: Select<Self::Currency>,
                    recv: Self::AccountId,
                    amount: Self::Balance,
                ) -> CallResult;
            }
            struct DefaultSelector<Runtime>(std::marker::PhantomData<Runtime>);
            struct RestrictedCurrency<Runtime>(std::marker::PhantomData<Runtime>);
            impl<Runtime: Pip20> frame_support::interface::Selector for DefaultSelector<Runtime> {
                type Selected = <Runtime as Pip20>::Currency;
                fn select(&self, from: sp_core::H256) -> SelectorResult<Self::Selected> {
                    ::core::panicking::panic("not yet implemented");
                }
            }
            impl<Runtime> DefaultSelector<Runtime> {
                pub fn new() -> Self {
                    DefaultSelector(Default::default())
                }
            }
            impl<Runtime: Pip20> frame_support::interface::Selector for RestrictedCurrency<Runtime> {
                type Selected = <Runtime as Pip20>::Currency;
                fn select(&self, from: sp_core::H256) -> SelectorResult<Self::Selected> {
                    ::core::panicking::panic("not yet implemented");
                }
            }
            impl<Runtime> RestrictedCurrency<Runtime> {
                pub fn new() -> Self {
                    RestrictedCurrency(Default::default())
                }
            }
            #[codec(encode_bound())]
            #[codec(decode_bound())]
            #[scale_info(skip_type_params(Runtime), capture_docs = "always")]
            #[allow(non_camel_case_types)]
            pub enum Call<Runtime: Pip20> {
                #[doc(hidden)]
                #[codec(skip)]
                __Ignore(
                    frame_support::sp_std::marker::PhantomData<(Runtime)>,
                    frame_support::Never,
                ),
                #[codec(index = 0u8)]
                transfer {
                    #[allow(missing_docs)]
                    recv: Runtime::AccountId,
                    #[allow(missing_docs)]
                    amount: Runtime::Balance,
                },
                #[codec(index = 3u8)]
                burn {
                    #[allow(missing_docs)]
                    from: Runtime::AccountId,
                    #[allow(missing_docs)]
                    amount: Runtime::Balance,
                },
                #[codec(index = 1u8)]
                approve {
                    #[allow(missing_docs)]
                    recv: Runtime::AccountId,
                    #[allow(missing_docs)]
                    amount: Runtime::Balance,
                },
            }
            const _: () = {
                impl<Runtime: Pip20> core::fmt::Debug for Call<Runtime> {
                    fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
                        match *self {
                            Self::__Ignore(ref _0, ref _1) => fmt
                                .debug_tuple("Call::__Ignore")
                                .field(&_0)
                                .field(&_1)
                                .finish(),
                            Self::transfer {
                                ref recv,
                                ref amount,
                            } => fmt
                                .debug_struct("Call::transfer")
                                .field("recv", &recv)
                                .field("amount", &amount)
                                .finish(),
                            Self::burn {
                                ref from,
                                ref amount,
                            } => fmt
                                .debug_struct("Call::burn")
                                .field("from", &from)
                                .field("amount", &amount)
                                .finish(),
                            Self::approve {
                                ref recv,
                                ref amount,
                            } => fmt
                                .debug_struct("Call::approve")
                                .field("recv", &recv)
                                .field("amount", &amount)
                                .finish(),
                        }
                    }
                }
            };
            const _: () = {
                impl<Runtime: Pip20> core::clone::Clone for Call<Runtime> {
                    fn clone(&self) -> Self {
                        match self {
                            Self::__Ignore(ref _0, ref _1) => Self::__Ignore(
                                core::clone::Clone::clone(_0),
                                core::clone::Clone::clone(_1),
                            ),
                            Self::transfer {
                                ref recv,
                                ref amount,
                            } => Self::transfer {
                                recv: core::clone::Clone::clone(recv),
                                amount: core::clone::Clone::clone(amount),
                            },
                            Self::burn {
                                ref from,
                                ref amount,
                            } => Self::burn {
                                from: core::clone::Clone::clone(from),
                                amount: core::clone::Clone::clone(amount),
                            },
                            Self::approve {
                                ref recv,
                                ref amount,
                            } => Self::approve {
                                recv: core::clone::Clone::clone(recv),
                                amount: core::clone::Clone::clone(amount),
                            },
                        }
                    }
                }
            };
            const _: () = {
                impl<Runtime: Pip20> core::cmp::Eq for Call<Runtime> {}
            };
            const _: () = {
                impl<Runtime: Pip20> core::cmp::PartialEq for Call<Runtime> {
                    fn eq(&self, other: &Self) -> bool {
                        match (self, other) {
                            (Self::__Ignore(_0, _1), Self::__Ignore(_0_other, _1_other)) => {
                                true && _0 == _0_other && _1 == _1_other
                            }
                            (
                                Self::transfer { recv, amount },
                                Self::transfer {
                                    recv: _0,
                                    amount: _1,
                                },
                            ) => true && recv == _0 && amount == _1,
                            (
                                Self::burn { from, amount },
                                Self::burn {
                                    from: _0,
                                    amount: _1,
                                },
                            ) => true && from == _0 && amount == _1,
                            (
                                Self::approve { recv, amount },
                                Self::approve {
                                    recv: _0,
                                    amount: _1,
                                },
                            ) => true && recv == _0 && amount == _1,
                            (Self::__Ignore { .. }, Self::transfer { .. }) => false,
                            (Self::__Ignore { .. }, Self::burn { .. }) => false,
                            (Self::__Ignore { .. }, Self::approve { .. }) => false,
                            (Self::transfer { .. }, Self::__Ignore { .. }) => false,
                            (Self::transfer { .. }, Self::burn { .. }) => false,
                            (Self::transfer { .. }, Self::approve { .. }) => false,
                            (Self::burn { .. }, Self::__Ignore { .. }) => false,
                            (Self::burn { .. }, Self::transfer { .. }) => false,
                            (Self::burn { .. }, Self::approve { .. }) => false,
                            (Self::approve { .. }, Self::__Ignore { .. }) => false,
                            (Self::approve { .. }, Self::transfer { .. }) => false,
                            (Self::approve { .. }, Self::burn { .. }) => false,
                        }
                    }
                }
            };
            #[allow(deprecated)]
            const _: () = {
                #[allow(non_camel_case_types)]
                #[automatically_derived]
                impl<Runtime: Pip20> ::codec::Encode for Call<Runtime> {
                    fn encode_to<__CodecOutputEdqy: ::codec::Output + ?::core::marker::Sized>(
                        &self,
                        __codec_dest_edqy: &mut __CodecOutputEdqy,
                    ) {
                        match *self {
                            Call::transfer {
                                ref recv,
                                ref amount,
                            } => {
                                __codec_dest_edqy.push_byte(0u8 as ::core::primitive::u8);
                                ::codec::Encode::encode_to(recv, __codec_dest_edqy);
                                ::codec::Encode::encode_to(amount, __codec_dest_edqy);
                            }
                            Call::burn {
                                ref from,
                                ref amount,
                            } => {
                                __codec_dest_edqy.push_byte(3u8 as ::core::primitive::u8);
                                ::codec::Encode::encode_to(from, __codec_dest_edqy);
                                ::codec::Encode::encode_to(amount, __codec_dest_edqy);
                            }
                            Call::approve {
                                ref recv,
                                ref amount,
                            } => {
                                __codec_dest_edqy.push_byte(1u8 as ::core::primitive::u8);
                                ::codec::Encode::encode_to(recv, __codec_dest_edqy);
                                ::codec::Encode::encode_to(amount, __codec_dest_edqy);
                            }
                            _ => (),
                        }
                    }
                }
                #[automatically_derived]
                impl<Runtime: Pip20> ::codec::EncodeLike for Call<Runtime> {}
            };
            #[allow(deprecated)]
            const _: () = {
                #[allow(non_camel_case_types)]
                #[automatically_derived]
                impl<Runtime: Pip20> ::codec::Decode for Call<Runtime> {
                    fn decode<__CodecInputEdqy: ::codec::Input>(
                        __codec_input_edqy: &mut __CodecInputEdqy,
                    ) -> ::core::result::Result<Self, ::codec::Error> {
                        match __codec_input_edqy.read_byte().map_err(|e| {
                            e.chain("Could not decode `Call`, failed to read variant byte")
                        })? {
                            __codec_x_edqy if __codec_x_edqy == 0u8 as ::core::primitive::u8 => {
                                ::core::result::Result::Ok(Call::<Runtime>::transfer {
                                    recv: {
                                        let __codec_res_edqy =
                                            <Runtime::AccountId as ::codec::Decode>::decode(
                                                __codec_input_edqy,
                                            );
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(e.chain(
                                                    "Could not decode `Call::transfer::recv`",
                                                ))
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                    amount: {
                                        let __codec_res_edqy =
                                            <Runtime::Balance as ::codec::Decode>::decode(
                                                __codec_input_edqy,
                                            );
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(e.chain(
                                                    "Could not decode `Call::transfer::amount`",
                                                ))
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                })
                            }
                            __codec_x_edqy if __codec_x_edqy == 3u8 as ::core::primitive::u8 => {
                                ::core::result::Result::Ok(Call::<Runtime>::burn {
                                    from: {
                                        let __codec_res_edqy =
                                            <Runtime::AccountId as ::codec::Decode>::decode(
                                                __codec_input_edqy,
                                            );
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(
                                                    e.chain("Could not decode `Call::burn::from`"),
                                                )
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                    amount: {
                                        let __codec_res_edqy =
                                            <Runtime::Balance as ::codec::Decode>::decode(
                                                __codec_input_edqy,
                                            );
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(e.chain(
                                                    "Could not decode `Call::burn::amount`",
                                                ))
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                })
                            }
                            __codec_x_edqy if __codec_x_edqy == 1u8 as ::core::primitive::u8 => {
                                ::core::result::Result::Ok(Call::<Runtime>::approve {
                                    recv: {
                                        let __codec_res_edqy =
                                            <Runtime::AccountId as ::codec::Decode>::decode(
                                                __codec_input_edqy,
                                            );
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(e.chain(
                                                    "Could not decode `Call::approve::recv`",
                                                ))
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                    amount: {
                                        let __codec_res_edqy =
                                            <Runtime::Balance as ::codec::Decode>::decode(
                                                __codec_input_edqy,
                                            );
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(e.chain(
                                                    "Could not decode `Call::approve::amount`",
                                                ))
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                })
                            }
                            _ => {
                                ::core::result::Result::Err(<_ as ::core::convert::Into<_>>::into(
                                    "Could not decode `Call`, variant doesn't exist",
                                ))
                            }
                        }
                    }
                }
            };
            #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
            const _: () = {
                impl<Runtime: Pip20> ::scale_info::TypeInfo for Call<Runtime>
                where
                    frame_support::sp_std::marker::PhantomData<(Runtime)>:
                        ::scale_info::TypeInfo + 'static,
                    Runtime::AccountId: ::scale_info::TypeInfo + 'static,
                    Runtime::Balance: ::scale_info::TypeInfo + 'static,
                    Runtime::AccountId: ::scale_info::TypeInfo + 'static,
                    Runtime::Balance: ::scale_info::TypeInfo + 'static,
                    Runtime::AccountId: ::scale_info::TypeInfo + 'static,
                    Runtime::Balance: ::scale_info::TypeInfo + 'static,
                    Runtime: Pip20 + 'static,
                {
                    type Identity = Self;
                    fn type_info() -> ::scale_info::Type {
                        ::scale_info::Type::builder()
                            .path(::scale_info::Path::new(
                                "Call",
                                "frame_support::interface::tests::int_123",
                            ))
                            .type_params(<[_]>::into_vec(
                                #[rustc_box]
                                ::alloc::boxed::Box::new([::scale_info::TypeParameter::new(
                                    "Runtime",
                                    ::core::option::Option::None,
                                )]),
                            ))
                            .variant(
                                ::scale_info::build::Variants::new()
                                    .variant("transfer", |v| {
                                        v.index(0u8 as ::core::primitive::u8).fields(
                                            ::scale_info::build::Fields::named()
                                                .field(|f| {
                                                    f.ty::<Runtime::AccountId>()
                                                        .name("recv")
                                                        .type_name("Runtime::AccountId")
                                                })
                                                .field(|f| {
                                                    f.ty::<Runtime::Balance>()
                                                        .name("amount")
                                                        .type_name("Runtime::Balance")
                                                }),
                                        )
                                    })
                                    .variant("burn", |v| {
                                        v.index(3u8 as ::core::primitive::u8).fields(
                                            ::scale_info::build::Fields::named()
                                                .field(|f| {
                                                    f.ty::<Runtime::AccountId>()
                                                        .name("from")
                                                        .type_name("Runtime::AccountId")
                                                })
                                                .field(|f| {
                                                    f.ty::<Runtime::Balance>()
                                                        .name("amount")
                                                        .type_name("Runtime::Balance")
                                                }),
                                        )
                                    })
                                    .variant("approve", |v| {
                                        v.index(1u8 as ::core::primitive::u8).fields(
                                            ::scale_info::build::Fields::named()
                                                .field(|f| {
                                                    f.ty::<Runtime::AccountId>()
                                                        .name("recv")
                                                        .type_name("Runtime::AccountId")
                                                })
                                                .field(|f| {
                                                    f.ty::<Runtime::Balance>()
                                                        .name("amount")
                                                        .type_name("Runtime::Balance")
                                                }),
                                        )
                                    }),
                            )
                    }
                };
            };
            impl<Runtime: Pip20> Call<Runtime> {
                ///Create a call with the variant `transfer`.
                pub fn new_call_variant_transfer(
                    recv: Runtime::AccountId,
                    amount: Runtime::Balance,
                ) -> Self {
                    Self::transfer { recv, amount }
                }
                ///Create a call with the variant `burn`.
                pub fn new_call_variant_burn(
                    from: Runtime::AccountId,
                    amount: Runtime::Balance,
                ) -> Self {
                    Self::burn { from, amount }
                }
                ///Create a call with the variant `approve`.
                pub fn new_call_variant_approve(
                    recv: Runtime::AccountId,
                    amount: Runtime::Balance,
                ) -> Self {
                    Self::approve { recv, amount }
                }
            }
            impl<Runtime: Pip20> frame_support::dispatch::GetDispatchInfo for Call<Runtime> {
                fn get_dispatch_info(&self) -> frame_support::dispatch::DispatchInfo {
                    match *self {
                        Self::transfer {
                            ref recv,
                            ref amount,
                        } => {
                            let __pallet_base_weight = 0;
                            let __pallet_weight = <dyn frame_support::dispatch::WeighData<(
                                &Runtime::AccountId,
                                &Runtime::Balance,
                            )>>::weigh_data(
                                &__pallet_base_weight, (recv, amount)
                            );
                            let __pallet_class = <dyn frame_support::dispatch::ClassifyDispatch<(
                                &Runtime::AccountId,
                                &Runtime::Balance,
                            )>>::classify_dispatch(
                                &__pallet_base_weight, (recv, amount)
                            );
                            let __pallet_pays_fee = <dyn frame_support::dispatch::PaysFee<(
                                &Runtime::AccountId,
                                &Runtime::Balance,
                            )>>::pays_fee(
                                &__pallet_base_weight, (recv, amount)
                            );
                            frame_support::dispatch::DispatchInfo {
                                weight: __pallet_weight,
                                class: __pallet_class,
                                pays_fee: __pallet_pays_fee,
                            }
                        }
                        Self::burn {
                            ref from,
                            ref amount,
                        } => {
                            let __pallet_base_weight = 0;
                            let __pallet_weight = <dyn frame_support::dispatch::WeighData<(
                                &Runtime::AccountId,
                                &Runtime::Balance,
                            )>>::weigh_data(
                                &__pallet_base_weight, (from, amount)
                            );
                            let __pallet_class = <dyn frame_support::dispatch::ClassifyDispatch<(
                                &Runtime::AccountId,
                                &Runtime::Balance,
                            )>>::classify_dispatch(
                                &__pallet_base_weight, (from, amount)
                            );
                            let __pallet_pays_fee = <dyn frame_support::dispatch::PaysFee<(
                                &Runtime::AccountId,
                                &Runtime::Balance,
                            )>>::pays_fee(
                                &__pallet_base_weight, (from, amount)
                            );
                            frame_support::dispatch::DispatchInfo {
                                weight: __pallet_weight,
                                class: __pallet_class,
                                pays_fee: __pallet_pays_fee,
                            }
                        }
                        Self::approve {
                            ref recv,
                            ref amount,
                        } => {
                            let __pallet_base_weight = 0;
                            let __pallet_weight = <dyn frame_support::dispatch::WeighData<(
                                &Runtime::AccountId,
                                &Runtime::Balance,
                            )>>::weigh_data(
                                &__pallet_base_weight, (recv, amount)
                            );
                            let __pallet_class = <dyn frame_support::dispatch::ClassifyDispatch<(
                                &Runtime::AccountId,
                                &Runtime::Balance,
                            )>>::classify_dispatch(
                                &__pallet_base_weight, (recv, amount)
                            );
                            let __pallet_pays_fee = <dyn frame_support::dispatch::PaysFee<(
                                &Runtime::AccountId,
                                &Runtime::Balance,
                            )>>::pays_fee(
                                &__pallet_base_weight, (recv, amount)
                            );
                            frame_support::dispatch::DispatchInfo {
                                weight: __pallet_weight,
                                class: __pallet_class,
                                pays_fee: __pallet_pays_fee,
                            }
                        }
                        Self::__Ignore(_, _) => ::core::panicking::panic_fmt(format_args!(
                            "internal error: entered unreachable code: {0}",
                            format_args!("__Ignore cannot be used")
                        )),
                    }
                }
            }
            #[allow(deprecated)]
            impl<Runtime: Pip20> frame_support::weights::GetDispatchInfo for Call<Runtime> {}
            impl<Runtime: Pip20> frame_support::dispatch::GetCallName for Call<Runtime> {
                fn get_call_name(&self) -> &'static str {
                    match *self {
                        Self::transfer { .. } => "transfer",
                        Self::burn { .. } => "burn",
                        Self::approve { .. } => "approve",
                        Self::__Ignore(_, _) => ::core::panicking::panic_fmt(format_args!(
                            "internal error: entered unreachable code: {0}",
                            format_args!("__PhantomItem cannot be used.")
                        )),
                    }
                }
                fn get_call_names() -> &'static [&'static str] {
                    &["transfer", "burn", "approve"]
                }
            }
            impl<Runtime: Pip20> frame_support::interface::Call for Call<Runtime> {
                type RuntimeOrigin = <Runtime as frame_support::interface::Core>::RuntimeOrigin;
                fn call(
                    self,
                    origin: Self::RuntimeOrigin,
                    selectable: sp_core::H256,
                ) -> frame_support::interface::CallResult {
                    frame_support::dispatch_context::run_in_context(|| match self {
                        Self::transfer { recv, amount } => {
                            let __within_span__ = {
                                use ::tracing::__macro_support::Callsite as _;
                                static CALLSITE: ::tracing::callsite::DefaultCallsite = {
                                    static META: ::tracing::Metadata<'static> = {
                                        ::tracing_core::metadata::Metadata::new(
                                            "transfer",
                                            "frame_support::interface::tests::int_123",
                                            ::tracing::Level::TRACE,
                                            Some("frame/support/src/interface.rs"),
                                            Some(185u32),
                                            Some("frame_support::interface::tests::int_123"),
                                            ::tracing_core::field::FieldSet::new(
                                                &[],
                                                ::tracing_core::callsite::Identifier(&CALLSITE),
                                            ),
                                            ::tracing::metadata::Kind::SPAN,
                                        )
                                    };
                                    ::tracing::callsite::DefaultCallsite::new(&META)
                                };
                                let mut interest = ::tracing::subscriber::Interest::never();
                                if ::tracing::Level::TRACE
                                    <= ::tracing::level_filters::STATIC_MAX_LEVEL
                                    && ::tracing::Level::TRACE
                                        <= ::tracing::level_filters::LevelFilter::current()
                                    && {
                                        interest = CALLSITE.interest();
                                        !interest.is_never()
                                    }
                                    && ::tracing::__macro_support::__is_enabled(
                                        CALLSITE.metadata(),
                                        interest,
                                    )
                                {
                                    let meta = CALLSITE.metadata();
                                    ::tracing::Span::new(meta, &{ meta.fields().value_set(&[]) })
                                } else {
                                    let span = ::tracing::__macro_support::__disabled_span(
                                        CALLSITE.metadata(),
                                    );
                                    {};
                                    span
                                }
                            };
                            let __tracing_guard__ = __within_span__.enter();
                            let select = frame_support::interface::Select::new(
                                selectable,
                                Box::new(DefaultSelector::<Runtime>::new()),
                            );
                            <Runtime as Pip20>::transfer(origin, select, recv, amount)
                                .map(Into::into)
                                .map_err(Into::into)
                        }
                        Self::burn { from, amount } => {
                            let __within_span__ = {
                                use ::tracing::__macro_support::Callsite as _;
                                static CALLSITE: ::tracing::callsite::DefaultCallsite = {
                                    static META: ::tracing::Metadata<'static> = {
                                        ::tracing_core::metadata::Metadata::new(
                                            "burn",
                                            "frame_support::interface::tests::int_123",
                                            ::tracing::Level::TRACE,
                                            Some("frame/support/src/interface.rs"),
                                            Some(185u32),
                                            Some("frame_support::interface::tests::int_123"),
                                            ::tracing_core::field::FieldSet::new(
                                                &[],
                                                ::tracing_core::callsite::Identifier(&CALLSITE),
                                            ),
                                            ::tracing::metadata::Kind::SPAN,
                                        )
                                    };
                                    ::tracing::callsite::DefaultCallsite::new(&META)
                                };
                                let mut interest = ::tracing::subscriber::Interest::never();
                                if ::tracing::Level::TRACE
                                    <= ::tracing::level_filters::STATIC_MAX_LEVEL
                                    && ::tracing::Level::TRACE
                                        <= ::tracing::level_filters::LevelFilter::current()
                                    && {
                                        interest = CALLSITE.interest();
                                        !interest.is_never()
                                    }
                                    && ::tracing::__macro_support::__is_enabled(
                                        CALLSITE.metadata(),
                                        interest,
                                    )
                                {
                                    let meta = CALLSITE.metadata();
                                    ::tracing::Span::new(meta, &{ meta.fields().value_set(&[]) })
                                } else {
                                    let span = ::tracing::__macro_support::__disabled_span(
                                        CALLSITE.metadata(),
                                    );
                                    {};
                                    span
                                }
                            };
                            let __tracing_guard__ = __within_span__.enter();
                            let select = frame_support::interface::Select::new(
                                selectable,
                                Box::new(frame_support::interface::EmptySelector::new()),
                            );
                            select.select()?;
                            <Runtime as Pip20>::burn(origin, from, amount)
                                .map(Into::into)
                                .map_err(Into::into)
                        }
                        Self::approve { recv, amount } => {
                            let __within_span__ = {
                                use ::tracing::__macro_support::Callsite as _;
                                static CALLSITE: ::tracing::callsite::DefaultCallsite = {
                                    static META: ::tracing::Metadata<'static> = {
                                        ::tracing_core::metadata::Metadata::new(
                                            "approve",
                                            "frame_support::interface::tests::int_123",
                                            ::tracing::Level::TRACE,
                                            Some("frame/support/src/interface.rs"),
                                            Some(185u32),
                                            Some("frame_support::interface::tests::int_123"),
                                            ::tracing_core::field::FieldSet::new(
                                                &[],
                                                ::tracing_core::callsite::Identifier(&CALLSITE),
                                            ),
                                            ::tracing::metadata::Kind::SPAN,
                                        )
                                    };
                                    ::tracing::callsite::DefaultCallsite::new(&META)
                                };
                                let mut interest = ::tracing::subscriber::Interest::never();
                                if ::tracing::Level::TRACE
                                    <= ::tracing::level_filters::STATIC_MAX_LEVEL
                                    && ::tracing::Level::TRACE
                                        <= ::tracing::level_filters::LevelFilter::current()
                                    && {
                                        interest = CALLSITE.interest();
                                        !interest.is_never()
                                    }
                                    && ::tracing::__macro_support::__is_enabled(
                                        CALLSITE.metadata(),
                                        interest,
                                    )
                                {
                                    let meta = CALLSITE.metadata();
                                    ::tracing::Span::new(meta, &{ meta.fields().value_set(&[]) })
                                } else {
                                    let span = ::tracing::__macro_support::__disabled_span(
                                        CALLSITE.metadata(),
                                    );
                                    {};
                                    span
                                }
                            };
                            let __tracing_guard__ = __within_span__.enter();
                            let select = frame_support::interface::Select::new(
                                selectable,
                                Box::new(RestrictedCurrency::<Runtime>::new()),
                            );
                            <Runtime as Pip20>::approve(origin, select, recv, amount)
                                .map(Into::into)
                                .map_err(Into::into)
                        }
                        Self::__Ignore(_, _) => {
                            let _ = origin;
                            ::core::panicking::panic_fmt(format_args!(
                                "internal error: entered unreachable code: {0}",
                                format_args!("__PhantomItem cannot be used.")
                            ));
                        }
                    })
                }
            }
            impl<Runtime: Pip20> Call<Runtime> {
                #[doc(hidden)]
                pub fn call_functions() -> frame_support::metadata::PalletCallMetadata {
                    frame_support::scale_info::meta_type::<Call<Runtime>>().into()
                }
            }
        }
    }
}
