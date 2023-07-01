mod mock {
    use crate as pallet_interface;
    use codec::{Decode, Encode};
    use frame_support::interface::{
        CallResult, Select, Selector, SelectorResult, ViewResult,
    };
    use frame_support::{
        assert_noop, assert_ok, ord_parameter_types, parameter_types,
        traits::{ConstU32, ConstU64, EitherOfDiverse},
        BoundedVec,
    };
    use frame_system::{EnsureRoot, EnsureSignedBy};
    use sp_core::H256;
    use sp_runtime::{testing::Header, traits::{BadOrigin, BlakeTwo256, IdentityLookup}};
    type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<MockRuntime>;
    type Block = frame_system::mocking::MockBlock<MockRuntime>;
    type Balance = u64;
    type AccountId = u64;
    enum CurrencyId {
        Native,
        Other,
    }
    mod interfaces {
        pub mod pip20 {
            use frame_support::{
                dispatch::DispatchResult,
                interface::{CallResult, Select, Selector, SelectorResult, ViewResult},
                Parameter,
            };
            use sp_core::H256;
            use sp_runtime::traits::Member;
            pub type CurrencySelectable = H256;
            pub type AccountIdSelectable = [u8; 32];
            pub type BalanceSelectable = u128;
            pub trait Pip20: frame_system::Config {
                /// A means for converting between from a [u8; 32] to the native chains account id.
                type SelectAccount: Selector<
                        Selectable = AccountIdSelectable,
                        Selected = Self::AccountId,
                    >
                    + Parameter
                    + Member;
                /// The chains native currency type.
                type Currency: Parameter + Member;
                /// A means for converting between from a `H256` to the chains native currency.
                type SelectCurrency: Selector<
                        Selectable = CurrencySelectable,
                        Selected = Self::Currency,
                    >
                    + Parameter
                    + Member;
                /// The chains native balance type.
                type Balance: Parameter + Member;
                /// A means for converting between from a u128 to the chains native balance.
                type SelectBalance: Selector<
                        Selectable = BalanceSelectable,
                        Selected = Self::Balance,
                    >
                    + Parameter
                    + Member;
                fn free_balance(
                    currency: Select<Self::SelectCurrency>,
                    who: Select<Self::SelectAccount>,
                ) -> ViewResult<BalanceSelectable>;
                fn balances(
                    who: Select<Self::SelectAccount>,
                ) -> ViewResult<Vec<(CurrencySelectable, BalanceSelectable)>>;
                fn transfer(
                    origin: Self::RuntimeOrigin,
                    currency: Self::SelectCurrency,
                    recv: Select<Self::SelectAccount>,
                    amount: Select<Self::SelectBalance>,
                ) -> CallResult;
                fn burn(
                    origin: Self::RuntimeOrigin,
                    currency: Select<SelectCurrency>,
                    from: Select<Self::SelectAccount>,
                    amount: Select<Self::SelectBalance>,
                ) -> CallResult;
                fn approve(
                    origin: Self::RuntimeOrigin,
                    currency: Select<RestrictedCurrency>,
                    recv: Select<Self::SelectAccount>,
                    amount: Select<Self::SelectBalance>,
                ) -> CallResult;
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
                    currency: Runtime::SelectCurrency,
                    #[allow(missing_docs)]
                    recv: Select<Runtime::SelectAccount>,
                    #[allow(missing_docs)]
                    amount: Select<Runtime::SelectBalance>,
                },
                #[codec(index = 3u8)]
                burn {
                    #[allow(missing_docs)]
                    currency: Select<SelectCurrency>,
                    #[allow(missing_docs)]
                    from: Select<Runtime::SelectAccount>,
                    #[allow(missing_docs)]
                    amount: Select<Runtime::SelectBalance>,
                },
                #[codec(index = 1u8)]
                approve {
                    #[allow(missing_docs)]
                    currency: Select<RestrictedCurrency>,
                    #[allow(missing_docs)]
                    recv: Select<Runtime::SelectAccount>,
                    #[allow(missing_docs)]
                    amount: Select<Runtime::SelectBalance>,
                },
            }
            const _: () = {
                impl<Runtime: Pip20> core::fmt::Debug for Call<Runtime> {
                    fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
                        match *self {
                            Self::__Ignore(ref _0, ref _1) => {
                                fmt.debug_tuple("Call::__Ignore")
                                    .field(&_0)
                                    .field(&_1)
                                    .finish()
                            }
                            Self::transfer { ref currency, ref recv, ref amount } => {
                                fmt.debug_struct("Call::transfer")
                                    .field("currency", &currency)
                                    .field("recv", &recv)
                                    .field("amount", &amount)
                                    .finish()
                            }
                            Self::burn { ref currency, ref from, ref amount } => {
                                fmt.debug_struct("Call::burn")
                                    .field("currency", &currency)
                                    .field("from", &from)
                                    .field("amount", &amount)
                                    .finish()
                            }
                            Self::approve { ref currency, ref recv, ref amount } => {
                                fmt.debug_struct("Call::approve")
                                    .field("currency", &currency)
                                    .field("recv", &recv)
                                    .field("amount", &amount)
                                    .finish()
                            }
                        }
                    }
                }
            };
            const _: () = {
                impl<Runtime: Pip20> core::clone::Clone for Call<Runtime> {
                    fn clone(&self) -> Self {
                        match self {
                            Self::__Ignore(ref _0, ref _1) => {
                                Self::__Ignore(
                                    core::clone::Clone::clone(_0),
                                    core::clone::Clone::clone(_1),
                                )
                            }
                            Self::transfer { ref currency, ref recv, ref amount } => {
                                Self::transfer {
                                    currency: core::clone::Clone::clone(currency),
                                    recv: core::clone::Clone::clone(recv),
                                    amount: core::clone::Clone::clone(amount),
                                }
                            }
                            Self::burn { ref currency, ref from, ref amount } => {
                                Self::burn {
                                    currency: core::clone::Clone::clone(currency),
                                    from: core::clone::Clone::clone(from),
                                    amount: core::clone::Clone::clone(amount),
                                }
                            }
                            Self::approve { ref currency, ref recv, ref amount } => {
                                Self::approve {
                                    currency: core::clone::Clone::clone(currency),
                                    recv: core::clone::Clone::clone(recv),
                                    amount: core::clone::Clone::clone(amount),
                                }
                            }
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
                            (
                                Self::__Ignore(_0, _1),
                                Self::__Ignore(_0_other, _1_other),
                            ) => true && _0 == _0_other && _1 == _1_other,
                            (
                                Self::transfer { currency, recv, amount },
                                Self::transfer { currency: _0, recv: _1, amount: _2 },
                            ) => true && currency == _0 && recv == _1 && amount == _2,
                            (
                                Self::burn { currency, from, amount },
                                Self::burn { currency: _0, from: _1, amount: _2 },
                            ) => true && currency == _0 && from == _1 && amount == _2,
                            (
                                Self::approve { currency, recv, amount },
                                Self::approve { currency: _0, recv: _1, amount: _2 },
                            ) => true && currency == _0 && recv == _1 && amount == _2,
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
                    fn encode_to<
                        __CodecOutputEdqy: ::codec::Output + ?::core::marker::Sized,
                    >(&self, __codec_dest_edqy: &mut __CodecOutputEdqy) {
                        match *self {
                            Call::transfer { ref currency, ref recv, ref amount } => {
                                __codec_dest_edqy.push_byte(0u8 as ::core::primitive::u8);
                                ::codec::Encode::encode_to(currency, __codec_dest_edqy);
                                ::codec::Encode::encode_to(recv, __codec_dest_edqy);
                                ::codec::Encode::encode_to(amount, __codec_dest_edqy);
                            }
                            Call::burn { ref currency, ref from, ref amount } => {
                                __codec_dest_edqy.push_byte(3u8 as ::core::primitive::u8);
                                ::codec::Encode::encode_to(currency, __codec_dest_edqy);
                                ::codec::Encode::encode_to(from, __codec_dest_edqy);
                                ::codec::Encode::encode_to(amount, __codec_dest_edqy);
                            }
                            Call::approve { ref currency, ref recv, ref amount } => {
                                __codec_dest_edqy.push_byte(1u8 as ::core::primitive::u8);
                                ::codec::Encode::encode_to(currency, __codec_dest_edqy);
                                ::codec::Encode::encode_to(recv, __codec_dest_edqy);
                                ::codec::Encode::encode_to(amount, __codec_dest_edqy);
                            }
                            _ => {}
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
                        match __codec_input_edqy
                            .read_byte()
                            .map_err(|e| {
                                e
                                    .chain(
                                        "Could not decode `Call`, failed to read variant byte",
                                    )
                            })?
                        {
                            __codec_x_edqy if __codec_x_edqy
                                == 0u8 as ::core::primitive::u8 => {
                                ::core::result::Result::Ok(Call::<Runtime>::transfer {
                                    currency: {
                                        let __codec_res_edqy = <Runtime::SelectCurrency as ::codec::Decode>::decode(
                                            __codec_input_edqy,
                                        );
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(
                                                    e.chain("Could not decode `Call::transfer::currency`"),
                                                );
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                    recv: {
                                        let __codec_res_edqy = <Select<
                                            Runtime::SelectAccount,
                                        > as ::codec::Decode>::decode(__codec_input_edqy);
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(
                                                    e.chain("Could not decode `Call::transfer::recv`"),
                                                );
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                    amount: {
                                        let __codec_res_edqy = <Select<
                                            Runtime::SelectBalance,
                                        > as ::codec::Decode>::decode(__codec_input_edqy);
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(
                                                    e.chain("Could not decode `Call::transfer::amount`"),
                                                );
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                })
                            }
                            __codec_x_edqy if __codec_x_edqy
                                == 3u8 as ::core::primitive::u8 => {
                                ::core::result::Result::Ok(Call::<Runtime>::burn {
                                    currency: {
                                        let __codec_res_edqy = <Select<
                                            SelectCurrency,
                                        > as ::codec::Decode>::decode(__codec_input_edqy);
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(
                                                    e.chain("Could not decode `Call::burn::currency`"),
                                                );
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                    from: {
                                        let __codec_res_edqy = <Select<
                                            Runtime::SelectAccount,
                                        > as ::codec::Decode>::decode(__codec_input_edqy);
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(
                                                    e.chain("Could not decode `Call::burn::from`"),
                                                );
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                    amount: {
                                        let __codec_res_edqy = <Select<
                                            Runtime::SelectBalance,
                                        > as ::codec::Decode>::decode(__codec_input_edqy);
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(
                                                    e.chain("Could not decode `Call::burn::amount`"),
                                                );
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                })
                            }
                            __codec_x_edqy if __codec_x_edqy
                                == 1u8 as ::core::primitive::u8 => {
                                ::core::result::Result::Ok(Call::<Runtime>::approve {
                                    currency: {
                                        let __codec_res_edqy = <Select<
                                            RestrictedCurrency,
                                        > as ::codec::Decode>::decode(__codec_input_edqy);
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(
                                                    e.chain("Could not decode `Call::approve::currency`"),
                                                );
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                    recv: {
                                        let __codec_res_edqy = <Select<
                                            Runtime::SelectAccount,
                                        > as ::codec::Decode>::decode(__codec_input_edqy);
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(
                                                    e.chain("Could not decode `Call::approve::recv`"),
                                                );
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                    amount: {
                                        let __codec_res_edqy = <Select<
                                            Runtime::SelectBalance,
                                        > as ::codec::Decode>::decode(__codec_input_edqy);
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(
                                                    e.chain("Could not decode `Call::approve::amount`"),
                                                );
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                })
                            }
                            _ => {
                                ::core::result::Result::Err(
                                    <_ as ::core::convert::Into<
                                        _,
                                    >>::into("Could not decode `Call`, variant doesn't exist"),
                                )
                            }
                        }
                    }
                }
            };
            #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
            const _: () = {
                impl<Runtime: Pip20> ::scale_info::TypeInfo for Call<Runtime>
                where
                    frame_support::sp_std::marker::PhantomData<
                        (Runtime),
                    >: ::scale_info::TypeInfo + 'static,
                    Runtime::SelectCurrency: ::scale_info::TypeInfo + 'static,
                    Select<Runtime::SelectAccount>: ::scale_info::TypeInfo + 'static,
                    Select<Runtime::SelectBalance>: ::scale_info::TypeInfo + 'static,
                    Select<Runtime::SelectAccount>: ::scale_info::TypeInfo + 'static,
                    Select<Runtime::SelectBalance>: ::scale_info::TypeInfo + 'static,
                    Select<Runtime::SelectAccount>: ::scale_info::TypeInfo + 'static,
                    Select<Runtime::SelectBalance>: ::scale_info::TypeInfo + 'static,
                    Runtime: Pip20 + 'static,
                {
                    type Identity = Self;
                    fn type_info() -> ::scale_info::Type {
                        ::scale_info::Type::builder()
                            .path(
                                ::scale_info::Path::new(
                                    "Call",
                                    "pallet_interface::mock::interfaces::pip20",
                                ),
                            )
                            .type_params(
                                <[_]>::into_vec(
                                    #[rustc_box]
                                    ::alloc::boxed::Box::new([
                                        ::scale_info::TypeParameter::new(
                                            "Runtime",
                                            ::core::option::Option::None,
                                        ),
                                    ]),
                                ),
                            )
                            .variant(
                                ::scale_info::build::Variants::new()
                                    .variant(
                                        "transfer",
                                        |v| {
                                            v
                                                .index(0u8 as ::core::primitive::u8)
                                                .fields(
                                                    ::scale_info::build::Fields::named()
                                                        .field(|f| {
                                                            f
                                                                .ty::<Runtime::SelectCurrency>()
                                                                .name("currency")
                                                                .type_name("Runtime::SelectCurrency")
                                                        })
                                                        .field(|f| {
                                                            f
                                                                .ty::<Select<Runtime::SelectAccount>>()
                                                                .name("recv")
                                                                .type_name("Select<Runtime::SelectAccount>")
                                                        })
                                                        .field(|f| {
                                                            f
                                                                .ty::<Select<Runtime::SelectBalance>>()
                                                                .name("amount")
                                                                .type_name("Select<Runtime::SelectBalance>")
                                                        }),
                                                )
                                        },
                                    )
                                    .variant(
                                        "burn",
                                        |v| {
                                            v
                                                .index(3u8 as ::core::primitive::u8)
                                                .fields(
                                                    ::scale_info::build::Fields::named()
                                                        .field(|f| {
                                                            f
                                                                .ty::<Select<SelectCurrency>>()
                                                                .name("currency")
                                                                .type_name("Select<SelectCurrency>")
                                                        })
                                                        .field(|f| {
                                                            f
                                                                .ty::<Select<Runtime::SelectAccount>>()
                                                                .name("from")
                                                                .type_name("Select<Runtime::SelectAccount>")
                                                        })
                                                        .field(|f| {
                                                            f
                                                                .ty::<Select<Runtime::SelectBalance>>()
                                                                .name("amount")
                                                                .type_name("Select<Runtime::SelectBalance>")
                                                        }),
                                                )
                                        },
                                    )
                                    .variant(
                                        "approve",
                                        |v| {
                                            v
                                                .index(1u8 as ::core::primitive::u8)
                                                .fields(
                                                    ::scale_info::build::Fields::named()
                                                        .field(|f| {
                                                            f
                                                                .ty::<Select<RestrictedCurrency>>()
                                                                .name("currency")
                                                                .type_name("Select<RestrictedCurrency>")
                                                        })
                                                        .field(|f| {
                                                            f
                                                                .ty::<Select<Runtime::SelectAccount>>()
                                                                .name("recv")
                                                                .type_name("Select<Runtime::SelectAccount>")
                                                        })
                                                        .field(|f| {
                                                            f
                                                                .ty::<Select<Runtime::SelectBalance>>()
                                                                .name("amount")
                                                                .type_name("Select<Runtime::SelectBalance>")
                                                        }),
                                                )
                                        },
                                    ),
                            )
                    }
                }
            };
            impl<Runtime: Pip20> Call<Runtime> {
                ///Create a call with the variant `transfer`.
                pub fn new_call_variant_transfer(
                    currency: Runtime::SelectCurrency,
                    recv: Select<Runtime::SelectAccount>,
                    amount: Select<Runtime::SelectBalance>,
                ) -> Self {
                    Self::transfer {
                        currency,
                        recv,
                        amount,
                    }
                }
                ///Create a call with the variant `burn`.
                pub fn new_call_variant_burn(
                    currency: Select<SelectCurrency>,
                    from: Select<Runtime::SelectAccount>,
                    amount: Select<Runtime::SelectBalance>,
                ) -> Self {
                    Self::burn {
                        currency,
                        from,
                        amount,
                    }
                }
                ///Create a call with the variant `approve`.
                pub fn new_call_variant_approve(
                    currency: Select<RestrictedCurrency>,
                    recv: Select<Runtime::SelectAccount>,
                    amount: Select<Runtime::SelectBalance>,
                ) -> Self {
                    Self::approve {
                        currency,
                        recv,
                        amount,
                    }
                }
            }
            impl<Runtime: Pip20> frame_support::dispatch::GetDispatchInfo
            for Call<Runtime> {
                fn get_dispatch_info(&self) -> frame_support::dispatch::DispatchInfo {
                    match *self {
                        Self::transfer { ref currency, ref recv, ref amount } => {
                            let __pallet_base_weight = 0;
                            let __pallet_weight = <dyn frame_support::dispatch::WeighData<
                                (
                                    &Runtime::SelectCurrency,
                                    &Select<Runtime::SelectAccount>,
                                    &Select<Runtime::SelectBalance>,
                                ),
                            >>::weigh_data(
                                &__pallet_base_weight,
                                (currency, recv, amount),
                            );
                            let __pallet_class = <dyn frame_support::dispatch::ClassifyDispatch<
                                (
                                    &Runtime::SelectCurrency,
                                    &Select<Runtime::SelectAccount>,
                                    &Select<Runtime::SelectBalance>,
                                ),
                            >>::classify_dispatch(
                                &__pallet_base_weight,
                                (currency, recv, amount),
                            );
                            let __pallet_pays_fee = <dyn frame_support::dispatch::PaysFee<
                                (
                                    &Runtime::SelectCurrency,
                                    &Select<Runtime::SelectAccount>,
                                    &Select<Runtime::SelectBalance>,
                                ),
                            >>::pays_fee(
                                &__pallet_base_weight,
                                (currency, recv, amount),
                            );
                            frame_support::dispatch::DispatchInfo {
                                weight: __pallet_weight,
                                class: __pallet_class,
                                pays_fee: __pallet_pays_fee,
                            }
                        }
                        Self::burn { ref currency, ref from, ref amount } => {
                            let __pallet_base_weight = 0;
                            let __pallet_weight = <dyn frame_support::dispatch::WeighData<
                                (
                                    &Select<SelectCurrency>,
                                    &Select<Runtime::SelectAccount>,
                                    &Select<Runtime::SelectBalance>,
                                ),
                            >>::weigh_data(
                                &__pallet_base_weight,
                                (currency, from, amount),
                            );
                            let __pallet_class = <dyn frame_support::dispatch::ClassifyDispatch<
                                (
                                    &Select<SelectCurrency>,
                                    &Select<Runtime::SelectAccount>,
                                    &Select<Runtime::SelectBalance>,
                                ),
                            >>::classify_dispatch(
                                &__pallet_base_weight,
                                (currency, from, amount),
                            );
                            let __pallet_pays_fee = <dyn frame_support::dispatch::PaysFee<
                                (
                                    &Select<SelectCurrency>,
                                    &Select<Runtime::SelectAccount>,
                                    &Select<Runtime::SelectBalance>,
                                ),
                            >>::pays_fee(
                                &__pallet_base_weight,
                                (currency, from, amount),
                            );
                            frame_support::dispatch::DispatchInfo {
                                weight: __pallet_weight,
                                class: __pallet_class,
                                pays_fee: __pallet_pays_fee,
                            }
                        }
                        Self::approve { ref currency, ref recv, ref amount } => {
                            let __pallet_base_weight = 0;
                            let __pallet_weight = <dyn frame_support::dispatch::WeighData<
                                (
                                    &Select<RestrictedCurrency>,
                                    &Select<Runtime::SelectAccount>,
                                    &Select<Runtime::SelectBalance>,
                                ),
                            >>::weigh_data(
                                &__pallet_base_weight,
                                (currency, recv, amount),
                            );
                            let __pallet_class = <dyn frame_support::dispatch::ClassifyDispatch<
                                (
                                    &Select<RestrictedCurrency>,
                                    &Select<Runtime::SelectAccount>,
                                    &Select<Runtime::SelectBalance>,
                                ),
                            >>::classify_dispatch(
                                &__pallet_base_weight,
                                (currency, recv, amount),
                            );
                            let __pallet_pays_fee = <dyn frame_support::dispatch::PaysFee<
                                (
                                    &Select<RestrictedCurrency>,
                                    &Select<Runtime::SelectAccount>,
                                    &Select<Runtime::SelectBalance>,
                                ),
                            >>::pays_fee(
                                &__pallet_base_weight,
                                (currency, recv, amount),
                            );
                            frame_support::dispatch::DispatchInfo {
                                weight: __pallet_weight,
                                class: __pallet_class,
                                pays_fee: __pallet_pays_fee,
                            }
                        }
                        Self::__Ignore(_, _) => {
                            ::core::panicking::panic_fmt(
                                format_args!(
                                    "internal error: entered unreachable code: {0}",
                                    format_args!("__Ignore cannot be used")
                                ),
                            );
                        }
                    }
                }
            }
            #[allow(deprecated)]
            impl<Runtime: Pip20> frame_support::weights::GetDispatchInfo
            for Call<Runtime> {}
            impl<Runtime: Pip20> frame_support::dispatch::GetCallName for Call<Runtime> {
                fn get_call_name(&self) -> &'static str {
                    match *self {
                        Self::transfer { .. } => "transfer",
                        Self::burn { .. } => "burn",
                        Self::approve { .. } => "approve",
                        Self::__Ignore(_, _) => {
                            ::core::panicking::panic_fmt(
                                format_args!(
                                    "internal error: entered unreachable code: {0}",
                                    format_args!("__PhantomItem cannot be used.")
                                ),
                            );
                        }
                    }
                }
                fn get_call_names() -> &'static [&'static str] {
                    &["transfer", "burn", "approve"]
                }
            }
            impl<Runtime: Pip20> frame_support::traits::UnfilteredDispatchable
            for Call<Runtime> {
                type RuntimeOrigin = <Runtime as frame_system::Config>::RuntimeOrigin;
                fn dispatch_bypass_filter(
                    self,
                    origin: Self::RuntimeOrigin,
                ) -> frame_support::dispatch::DispatchResultWithPostInfo {
                    frame_support::dispatch_context::run_in_context(|| {
                        match self {
                            Self::transfer { currency, recv, amount } => {
                                let __within_span__ = {
                                    use ::tracing::__macro_support::Callsite as _;
                                    static CALLSITE: ::tracing::callsite::DefaultCallsite = {
                                        static META: ::tracing::Metadata<'static> = {
                                            ::tracing_core::metadata::Metadata::new(
                                                "transfer",
                                                "pallet_interface::mock::interfaces::pip20",
                                                ::tracing::Level::TRACE,
                                                Some("frame/interface/src/mock.rs"),
                                                Some(44u32),
                                                Some("pallet_interface::mock::interfaces::pip20"),
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
                                        ::tracing::Span::new(
                                            meta,
                                            &{ meta.fields().value_set(&[]) },
                                        )
                                    } else {
                                        let span = ::tracing::__macro_support::__disabled_span(
                                            CALLSITE.metadata(),
                                        );
                                        {};
                                        span
                                    }
                                };
                                let __tracing_guard__ = __within_span__.enter();
                                <Runtime as Pip20>::transfer(origin, currency, recv, amount)
                                    .map(Into::into)
                                    .map_err(Into::into)
                            }
                            Self::burn { currency, from, amount } => {
                                let __within_span__ = {
                                    use ::tracing::__macro_support::Callsite as _;
                                    static CALLSITE: ::tracing::callsite::DefaultCallsite = {
                                        static META: ::tracing::Metadata<'static> = {
                                            ::tracing_core::metadata::Metadata::new(
                                                "burn",
                                                "pallet_interface::mock::interfaces::pip20",
                                                ::tracing::Level::TRACE,
                                                Some("frame/interface/src/mock.rs"),
                                                Some(44u32),
                                                Some("pallet_interface::mock::interfaces::pip20"),
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
                                        ::tracing::Span::new(
                                            meta,
                                            &{ meta.fields().value_set(&[]) },
                                        )
                                    } else {
                                        let span = ::tracing::__macro_support::__disabled_span(
                                            CALLSITE.metadata(),
                                        );
                                        {};
                                        span
                                    }
                                };
                                let __tracing_guard__ = __within_span__.enter();
                                <Runtime as Pip20>::burn(origin, currency, from, amount)
                                    .map(Into::into)
                                    .map_err(Into::into)
                            }
                            Self::approve { currency, recv, amount } => {
                                let __within_span__ = {
                                    use ::tracing::__macro_support::Callsite as _;
                                    static CALLSITE: ::tracing::callsite::DefaultCallsite = {
                                        static META: ::tracing::Metadata<'static> = {
                                            ::tracing_core::metadata::Metadata::new(
                                                "approve",
                                                "pallet_interface::mock::interfaces::pip20",
                                                ::tracing::Level::TRACE,
                                                Some("frame/interface/src/mock.rs"),
                                                Some(44u32),
                                                Some("pallet_interface::mock::interfaces::pip20"),
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
                                        ::tracing::Span::new(
                                            meta,
                                            &{ meta.fields().value_set(&[]) },
                                        )
                                    } else {
                                        let span = ::tracing::__macro_support::__disabled_span(
                                            CALLSITE.metadata(),
                                        );
                                        {};
                                        span
                                    }
                                };
                                let __tracing_guard__ = __within_span__.enter();
                                <Runtime as Pip20>::approve(origin, currency, recv, amount)
                                    .map(Into::into)
                                    .map_err(Into::into)
                            }
                            Self::__Ignore(_, _) => {
                                let _ = origin;
                                {
                                    ::core::panicking::panic_fmt(
                                        format_args!(
                                            "internal error: entered unreachable code: {0}",
                                            format_args!("__PhantomItem cannot be used.")
                                        ),
                                    );
                                };
                            }
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
            #[codec(encode_bound())]
            #[codec(decode_bound())]
            #[scale_info(skip_type_params(Runtime), capture_docs = "always")]
            #[allow(non_camel_case_types)]
            pub enum View<Runtime: Pip20> {
                #[doc(hidden)]
                #[codec(skip)]
                __Ignore(
                    frame_support::sp_std::marker::PhantomData<(Runtime)>,
                    frame_support::Never,
                ),
                #[codec(index = 0u8)]
                free_balance {
                    #[allow(missing_docs)]
                    currency: Select<Runtime::SelectCurrency>,
                    #[allow(missing_docs)]
                    who: Select<Runtime::SelectAccount>,
                },
                #[codec(index = 1u8)]
                balances { #[allow(missing_docs)] who: Select<Runtime::SelectAccount> },
            }
            const _: () = {
                impl<Runtime: Pip20> core::fmt::Debug for View<Runtime> {
                    fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
                        match *self {
                            Self::__Ignore(ref _0, ref _1) => {
                                fmt.debug_tuple("View::__Ignore")
                                    .field(&_0)
                                    .field(&_1)
                                    .finish()
                            }
                            Self::free_balance { ref currency, ref who } => {
                                fmt.debug_struct("View::free_balance")
                                    .field("currency", &currency)
                                    .field("who", &who)
                                    .finish()
                            }
                            Self::balances { ref who } => {
                                fmt.debug_struct("View::balances")
                                    .field("who", &who)
                                    .finish()
                            }
                        }
                    }
                }
            };
            const _: () = {
                impl<Runtime: Pip20> core::clone::Clone for View<Runtime> {
                    fn clone(&self) -> Self {
                        match self {
                            Self::__Ignore(ref _0, ref _1) => {
                                Self::__Ignore(
                                    core::clone::Clone::clone(_0),
                                    core::clone::Clone::clone(_1),
                                )
                            }
                            Self::free_balance { ref currency, ref who } => {
                                Self::free_balance {
                                    currency: core::clone::Clone::clone(currency),
                                    who: core::clone::Clone::clone(who),
                                }
                            }
                            Self::balances { ref who } => {
                                Self::balances {
                                    who: core::clone::Clone::clone(who),
                                }
                            }
                        }
                    }
                }
            };
            const _: () = {
                impl<Runtime: Pip20> core::cmp::Eq for View<Runtime> {}
            };
            const _: () = {
                impl<Runtime: Pip20> core::cmp::PartialEq for View<Runtime> {
                    fn eq(&self, other: &Self) -> bool {
                        match (self, other) {
                            (
                                Self::__Ignore(_0, _1),
                                Self::__Ignore(_0_other, _1_other),
                            ) => true && _0 == _0_other && _1 == _1_other,
                            (
                                Self::free_balance { currency, who },
                                Self::free_balance { currency: _0, who: _1 },
                            ) => true && currency == _0 && who == _1,
                            (Self::balances { who }, Self::balances { who: _0 }) => {
                                true && who == _0
                            }
                            (Self::__Ignore { .. }, Self::free_balance { .. }) => false,
                            (Self::__Ignore { .. }, Self::balances { .. }) => false,
                            (Self::free_balance { .. }, Self::__Ignore { .. }) => false,
                            (Self::free_balance { .. }, Self::balances { .. }) => false,
                            (Self::balances { .. }, Self::__Ignore { .. }) => false,
                            (Self::balances { .. }, Self::free_balance { .. }) => false,
                        }
                    }
                }
            };
            #[allow(deprecated)]
            const _: () = {
                #[allow(non_camel_case_types)]
                #[automatically_derived]
                impl<Runtime: Pip20> ::codec::Encode for View<Runtime> {
                    fn encode_to<
                        __CodecOutputEdqy: ::codec::Output + ?::core::marker::Sized,
                    >(&self, __codec_dest_edqy: &mut __CodecOutputEdqy) {
                        match *self {
                            View::free_balance { ref currency, ref who } => {
                                __codec_dest_edqy.push_byte(0u8 as ::core::primitive::u8);
                                ::codec::Encode::encode_to(currency, __codec_dest_edqy);
                                ::codec::Encode::encode_to(who, __codec_dest_edqy);
                            }
                            View::balances { ref who } => {
                                __codec_dest_edqy.push_byte(1u8 as ::core::primitive::u8);
                                ::codec::Encode::encode_to(who, __codec_dest_edqy);
                            }
                            _ => {}
                        }
                    }
                }
                #[automatically_derived]
                impl<Runtime: Pip20> ::codec::EncodeLike for View<Runtime> {}
            };
            #[allow(deprecated)]
            const _: () = {
                #[allow(non_camel_case_types)]
                #[automatically_derived]
                impl<Runtime: Pip20> ::codec::Decode for View<Runtime> {
                    fn decode<__CodecInputEdqy: ::codec::Input>(
                        __codec_input_edqy: &mut __CodecInputEdqy,
                    ) -> ::core::result::Result<Self, ::codec::Error> {
                        match __codec_input_edqy
                            .read_byte()
                            .map_err(|e| {
                                e
                                    .chain(
                                        "Could not decode `View`, failed to read variant byte",
                                    )
                            })?
                        {
                            __codec_x_edqy if __codec_x_edqy
                                == 0u8 as ::core::primitive::u8 => {
                                ::core::result::Result::Ok(View::<Runtime>::free_balance {
                                    currency: {
                                        let __codec_res_edqy = <Select<
                                            Runtime::SelectCurrency,
                                        > as ::codec::Decode>::decode(__codec_input_edqy);
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(
                                                    e.chain("Could not decode `View::free_balance::currency`"),
                                                );
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                    who: {
                                        let __codec_res_edqy = <Select<
                                            Runtime::SelectAccount,
                                        > as ::codec::Decode>::decode(__codec_input_edqy);
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(
                                                    e.chain("Could not decode `View::free_balance::who`"),
                                                );
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                })
                            }
                            __codec_x_edqy if __codec_x_edqy
                                == 1u8 as ::core::primitive::u8 => {
                                ::core::result::Result::Ok(View::<Runtime>::balances {
                                    who: {
                                        let __codec_res_edqy = <Select<
                                            Runtime::SelectAccount,
                                        > as ::codec::Decode>::decode(__codec_input_edqy);
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(
                                                    e.chain("Could not decode `View::balances::who`"),
                                                );
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                })
                            }
                            _ => {
                                ::core::result::Result::Err(
                                    <_ as ::core::convert::Into<
                                        _,
                                    >>::into("Could not decode `View`, variant doesn't exist"),
                                )
                            }
                        }
                    }
                }
            };
            #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
            const _: () = {
                impl<Runtime: Pip20> ::scale_info::TypeInfo for View<Runtime>
                where
                    frame_support::sp_std::marker::PhantomData<
                        (Runtime),
                    >: ::scale_info::TypeInfo + 'static,
                    Select<Runtime::SelectCurrency>: ::scale_info::TypeInfo + 'static,
                    Select<Runtime::SelectAccount>: ::scale_info::TypeInfo + 'static,
                    Select<Runtime::SelectAccount>: ::scale_info::TypeInfo + 'static,
                    Runtime: Pip20 + 'static,
                {
                    type Identity = Self;
                    fn type_info() -> ::scale_info::Type {
                        ::scale_info::Type::builder()
                            .path(
                                ::scale_info::Path::new(
                                    "View",
                                    "pallet_interface::mock::interfaces::pip20",
                                ),
                            )
                            .type_params(
                                <[_]>::into_vec(
                                    #[rustc_box]
                                    ::alloc::boxed::Box::new([
                                        ::scale_info::TypeParameter::new(
                                            "Runtime",
                                            ::core::option::Option::None,
                                        ),
                                    ]),
                                ),
                            )
                            .variant(
                                ::scale_info::build::Variants::new()
                                    .variant(
                                        "free_balance",
                                        |v| {
                                            v
                                                .index(0u8 as ::core::primitive::u8)
                                                .fields(
                                                    ::scale_info::build::Fields::named()
                                                        .field(|f| {
                                                            f
                                                                .ty::<Select<Runtime::SelectCurrency>>()
                                                                .name("currency")
                                                                .type_name("Select<Runtime::SelectCurrency>")
                                                        })
                                                        .field(|f| {
                                                            f
                                                                .ty::<Select<Runtime::SelectAccount>>()
                                                                .name("who")
                                                                .type_name("Select<Runtime::SelectAccount>")
                                                        }),
                                                )
                                        },
                                    )
                                    .variant(
                                        "balances",
                                        |v| {
                                            v
                                                .index(1u8 as ::core::primitive::u8)
                                                .fields(
                                                    ::scale_info::build::Fields::named()
                                                        .field(|f| {
                                                            f
                                                                .ty::<Select<Runtime::SelectAccount>>()
                                                                .name("who")
                                                                .type_name("Select<Runtime::SelectAccount>")
                                                        }),
                                                )
                                        },
                                    ),
                            )
                    }
                }
            };
            impl<Runtime: Pip20> View<Runtime> {
                ///Create a view with the variant `free_balance`.
                pub fn new_view_variant_free_balance(
                    currency: Select<Runtime::SelectCurrency>,
                    who: Select<Runtime::SelectAccount>,
                ) -> Self {
                    Self::free_balance {
                        currency,
                        who,
                    }
                }
                ///Create a view with the variant `balances`.
                pub fn new_view_variant_balances(
                    who: Select<Runtime::SelectAccount>,
                ) -> Self {
                    Self::balances { who }
                }
            }
            impl<Runtime: Pip20> frame_support::interface::View for View<Runtime> {
                fn view(self) -> frame_support::interface::ViewResult<Vec<u8>> {
                    match self {
                        Self::free_balance { currency, who } => {
                            let __within_span__ = {
                                use ::tracing::__macro_support::Callsite as _;
                                static CALLSITE: ::tracing::callsite::DefaultCallsite = {
                                    static META: ::tracing::Metadata<'static> = {
                                        ::tracing_core::metadata::Metadata::new(
                                            "free_balance",
                                            "pallet_interface::mock::interfaces::pip20",
                                            ::tracing::Level::TRACE,
                                            Some("frame/interface/src/mock.rs"),
                                            Some(44u32),
                                            Some("pallet_interface::mock::interfaces::pip20"),
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
                                    ::tracing::Span::new(
                                        meta,
                                        &{ meta.fields().value_set(&[]) },
                                    )
                                } else {
                                    let span = ::tracing::__macro_support::__disabled_span(
                                        CALLSITE.metadata(),
                                    );
                                    {};
                                    span
                                }
                            };
                            let __tracing_guard__ = __within_span__.enter();
                            <Runtime as Pip20>::free_balance(currency, who)
                                .map(|ty| frame_support::codec::Encode::encode(&ty))
                                .map_err(Into::into)
                        }
                        Self::balances { who } => {
                            let __within_span__ = {
                                use ::tracing::__macro_support::Callsite as _;
                                static CALLSITE: ::tracing::callsite::DefaultCallsite = {
                                    static META: ::tracing::Metadata<'static> = {
                                        ::tracing_core::metadata::Metadata::new(
                                            "balances",
                                            "pallet_interface::mock::interfaces::pip20",
                                            ::tracing::Level::TRACE,
                                            Some("frame/interface/src/mock.rs"),
                                            Some(44u32),
                                            Some("pallet_interface::mock::interfaces::pip20"),
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
                                    ::tracing::Span::new(
                                        meta,
                                        &{ meta.fields().value_set(&[]) },
                                    )
                                } else {
                                    let span = ::tracing::__macro_support::__disabled_span(
                                        CALLSITE.metadata(),
                                    );
                                    {};
                                    span
                                }
                            };
                            let __tracing_guard__ = __within_span__.enter();
                            <Runtime as Pip20>::balances(who)
                                .map(|ty| frame_support::codec::Encode::encode(&ty))
                                .map_err(Into::into)
                        }
                        Self::__Ignore(_, _) => {
                            {
                                ::core::panicking::panic_fmt(
                                    format_args!(
                                        "internal error: entered unreachable code: {0}",
                                        format_args!("__PhantomItem cannot be used.")
                                    ),
                                );
                            };
                        }
                    }
                }
            }
            impl<Runtime: Pip20> View<Runtime> {
                #[doc(hidden)]
                pub fn call_functions() -> frame_support::metadata::PalletCallMetadata {
                    frame_support::scale_info::meta_type::<View<Runtime>>().into()
                }
            }
        }
        pub mod pip42 {
            use frame_support::interface;
            use frame_support::interface::CallResult;
            use sp_core::Get;
            use sp_runtime::BoundedVec;
            pub trait Pip42: frame_system::Config {
                type MaxRemark: Get<u32>;
                fn remark(
                    origin: Self::RuntimeOrigin,
                    bytes: BoundedVec<u8, Self::MaxRemark>,
                ) -> CallResult;
            }
            #[codec(encode_bound())]
            #[codec(decode_bound())]
            #[scale_info(skip_type_params(Runtime), capture_docs = "always")]
            #[allow(non_camel_case_types)]
            pub enum Call<Runtime: Pip42> {
                #[doc(hidden)]
                #[codec(skip)]
                __Ignore(
                    frame_support::sp_std::marker::PhantomData<(Runtime)>,
                    frame_support::Never,
                ),
                #[codec(index = 0u8)]
                remark {
                    #[allow(missing_docs)]
                    bytes: BoundedVec<u8, Runtime::MaxRemark>,
                },
            }
            const _: () = {
                impl<Runtime: Pip42> core::fmt::Debug for Call<Runtime> {
                    fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
                        match *self {
                            Self::__Ignore(ref _0, ref _1) => {
                                fmt.debug_tuple("Call::__Ignore")
                                    .field(&_0)
                                    .field(&_1)
                                    .finish()
                            }
                            Self::remark { ref bytes } => {
                                fmt.debug_struct("Call::remark")
                                    .field("bytes", &bytes)
                                    .finish()
                            }
                        }
                    }
                }
            };
            const _: () = {
                impl<Runtime: Pip42> core::clone::Clone for Call<Runtime> {
                    fn clone(&self) -> Self {
                        match self {
                            Self::__Ignore(ref _0, ref _1) => {
                                Self::__Ignore(
                                    core::clone::Clone::clone(_0),
                                    core::clone::Clone::clone(_1),
                                )
                            }
                            Self::remark { ref bytes } => {
                                Self::remark {
                                    bytes: core::clone::Clone::clone(bytes),
                                }
                            }
                        }
                    }
                }
            };
            const _: () = {
                impl<Runtime: Pip42> core::cmp::Eq for Call<Runtime> {}
            };
            const _: () = {
                impl<Runtime: Pip42> core::cmp::PartialEq for Call<Runtime> {
                    fn eq(&self, other: &Self) -> bool {
                        match (self, other) {
                            (
                                Self::__Ignore(_0, _1),
                                Self::__Ignore(_0_other, _1_other),
                            ) => true && _0 == _0_other && _1 == _1_other,
                            (Self::remark { bytes }, Self::remark { bytes: _0 }) => {
                                true && bytes == _0
                            }
                            (Self::__Ignore { .. }, Self::remark { .. }) => false,
                            (Self::remark { .. }, Self::__Ignore { .. }) => false,
                        }
                    }
                }
            };
            #[allow(deprecated)]
            const _: () = {
                #[allow(non_camel_case_types)]
                #[automatically_derived]
                impl<Runtime: Pip42> ::codec::Encode for Call<Runtime> {
                    fn encode_to<
                        __CodecOutputEdqy: ::codec::Output + ?::core::marker::Sized,
                    >(&self, __codec_dest_edqy: &mut __CodecOutputEdqy) {
                        match *self {
                            Call::remark { ref bytes } => {
                                __codec_dest_edqy.push_byte(0u8 as ::core::primitive::u8);
                                ::codec::Encode::encode_to(bytes, __codec_dest_edqy);
                            }
                            _ => {}
                        }
                    }
                }
                #[automatically_derived]
                impl<Runtime: Pip42> ::codec::EncodeLike for Call<Runtime> {}
            };
            #[allow(deprecated)]
            const _: () = {
                #[allow(non_camel_case_types)]
                #[automatically_derived]
                impl<Runtime: Pip42> ::codec::Decode for Call<Runtime> {
                    fn decode<__CodecInputEdqy: ::codec::Input>(
                        __codec_input_edqy: &mut __CodecInputEdqy,
                    ) -> ::core::result::Result<Self, ::codec::Error> {
                        match __codec_input_edqy
                            .read_byte()
                            .map_err(|e| {
                                e
                                    .chain(
                                        "Could not decode `Call`, failed to read variant byte",
                                    )
                            })?
                        {
                            __codec_x_edqy if __codec_x_edqy
                                == 0u8 as ::core::primitive::u8 => {
                                ::core::result::Result::Ok(Call::<Runtime>::remark {
                                    bytes: {
                                        let __codec_res_edqy = <BoundedVec<
                                            u8,
                                            Runtime::MaxRemark,
                                        > as ::codec::Decode>::decode(__codec_input_edqy);
                                        match __codec_res_edqy {
                                            ::core::result::Result::Err(e) => {
                                                return ::core::result::Result::Err(
                                                    e.chain("Could not decode `Call::remark::bytes`"),
                                                );
                                            }
                                            ::core::result::Result::Ok(__codec_res_edqy) => {
                                                __codec_res_edqy
                                            }
                                        }
                                    },
                                })
                            }
                            _ => {
                                ::core::result::Result::Err(
                                    <_ as ::core::convert::Into<
                                        _,
                                    >>::into("Could not decode `Call`, variant doesn't exist"),
                                )
                            }
                        }
                    }
                }
            };
            #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
            const _: () = {
                impl<Runtime: Pip42> ::scale_info::TypeInfo for Call<Runtime>
                where
                    frame_support::sp_std::marker::PhantomData<
                        (Runtime),
                    >: ::scale_info::TypeInfo + 'static,
                    BoundedVec<u8, Runtime::MaxRemark>: ::scale_info::TypeInfo + 'static,
                    Runtime: Pip42 + 'static,
                {
                    type Identity = Self;
                    fn type_info() -> ::scale_info::Type {
                        ::scale_info::Type::builder()
                            .path(
                                ::scale_info::Path::new(
                                    "Call",
                                    "pallet_interface::mock::interfaces::pip42",
                                ),
                            )
                            .type_params(
                                <[_]>::into_vec(
                                    #[rustc_box]
                                    ::alloc::boxed::Box::new([
                                        ::scale_info::TypeParameter::new(
                                            "Runtime",
                                            ::core::option::Option::None,
                                        ),
                                    ]),
                                ),
                            )
                            .variant(
                                ::scale_info::build::Variants::new()
                                    .variant(
                                        "remark",
                                        |v| {
                                            v
                                                .index(0u8 as ::core::primitive::u8)
                                                .fields(
                                                    ::scale_info::build::Fields::named()
                                                        .field(|f| {
                                                            f
                                                                .ty::<BoundedVec<u8, Runtime::MaxRemark>>()
                                                                .name("bytes")
                                                                .type_name("BoundedVec<u8, Runtime::MaxRemark>")
                                                        }),
                                                )
                                        },
                                    ),
                            )
                    }
                }
            };
            impl<Runtime: Pip42> Call<Runtime> {
                ///Create a call with the variant `remark`.
                pub fn new_call_variant_remark(
                    bytes: BoundedVec<u8, Runtime::MaxRemark>,
                ) -> Self {
                    Self::remark { bytes }
                }
            }
            impl<Runtime: Pip42> frame_support::dispatch::GetDispatchInfo
            for Call<Runtime> {
                fn get_dispatch_info(&self) -> frame_support::dispatch::DispatchInfo {
                    match *self {
                        Self::remark { ref bytes } => {
                            let __pallet_base_weight = 0;
                            let __pallet_weight = <dyn frame_support::dispatch::WeighData<
                                (&BoundedVec<u8, Runtime::MaxRemark>,),
                            >>::weigh_data(&__pallet_base_weight, (bytes,));
                            let __pallet_class = <dyn frame_support::dispatch::ClassifyDispatch<
                                (&BoundedVec<u8, Runtime::MaxRemark>,),
                            >>::classify_dispatch(&__pallet_base_weight, (bytes,));
                            let __pallet_pays_fee = <dyn frame_support::dispatch::PaysFee<
                                (&BoundedVec<u8, Runtime::MaxRemark>,),
                            >>::pays_fee(&__pallet_base_weight, (bytes,));
                            frame_support::dispatch::DispatchInfo {
                                weight: __pallet_weight,
                                class: __pallet_class,
                                pays_fee: __pallet_pays_fee,
                            }
                        }
                        Self::__Ignore(_, _) => {
                            ::core::panicking::panic_fmt(
                                format_args!(
                                    "internal error: entered unreachable code: {0}",
                                    format_args!("__Ignore cannot be used")
                                ),
                            );
                        }
                    }
                }
            }
            #[allow(deprecated)]
            impl<Runtime: Pip42> frame_support::weights::GetDispatchInfo
            for Call<Runtime> {}
            impl<Runtime: Pip42> frame_support::dispatch::GetCallName for Call<Runtime> {
                fn get_call_name(&self) -> &'static str {
                    match *self {
                        Self::remark { .. } => "remark",
                        Self::__Ignore(_, _) => {
                            ::core::panicking::panic_fmt(
                                format_args!(
                                    "internal error: entered unreachable code: {0}",
                                    format_args!("__PhantomItem cannot be used.")
                                ),
                            );
                        }
                    }
                }
                fn get_call_names() -> &'static [&'static str] {
                    &["remark"]
                }
            }
            impl<Runtime: Pip42> frame_support::traits::UnfilteredDispatchable
            for Call<Runtime> {
                type RuntimeOrigin = <Runtime as frame_system::Config>::RuntimeOrigin;
                fn dispatch_bypass_filter(
                    self,
                    origin: Self::RuntimeOrigin,
                ) -> frame_support::dispatch::DispatchResultWithPostInfo {
                    frame_support::dispatch_context::run_in_context(|| {
                        match self {
                            Self::remark { bytes } => {
                                let __within_span__ = {
                                    use ::tracing::__macro_support::Callsite as _;
                                    static CALLSITE: ::tracing::callsite::DefaultCallsite = {
                                        static META: ::tracing::Metadata<'static> = {
                                            ::tracing_core::metadata::Metadata::new(
                                                "remark",
                                                "pallet_interface::mock::interfaces::pip42",
                                                ::tracing::Level::TRACE,
                                                Some("frame/interface/src/mock.rs"),
                                                Some(126u32),
                                                Some("pallet_interface::mock::interfaces::pip42"),
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
                                        ::tracing::Span::new(
                                            meta,
                                            &{ meta.fields().value_set(&[]) },
                                        )
                                    } else {
                                        let span = ::tracing::__macro_support::__disabled_span(
                                            CALLSITE.metadata(),
                                        );
                                        {};
                                        span
                                    }
                                };
                                let __tracing_guard__ = __within_span__.enter();
                                <Runtime as Pip42>::remark(origin, bytes)
                                    .map(Into::into)
                                    .map_err(Into::into)
                            }
                            Self::__Ignore(_, _) => {
                                let _ = origin;
                                {
                                    ::core::panicking::panic_fmt(
                                        format_args!(
                                            "internal error: entered unreachable code: {0}",
                                            format_args!("__PhantomItem cannot be used.")
                                        ),
                                    );
                                };
                            }
                        }
                    })
                }
            }
            impl<Runtime: Pip42> Call<Runtime> {
                #[doc(hidden)]
                pub fn call_functions() -> frame_support::metadata::PalletCallMetadata {
                    frame_support::scale_info::meta_type::<Call<Runtime>>().into()
                }
            }
            #[codec(encode_bound())]
            #[codec(decode_bound())]
            #[scale_info(skip_type_params(Runtime), capture_docs = "always")]
            #[allow(non_camel_case_types)]
            pub enum View<Runtime: Pip42> {
                #[doc(hidden)]
                #[codec(skip)]
                __Ignore(
                    frame_support::sp_std::marker::PhantomData<(Runtime)>,
                    frame_support::Never,
                ),
            }
            const _: () = {
                impl<Runtime: Pip42> core::fmt::Debug for View<Runtime> {
                    fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
                        match *self {
                            Self::__Ignore(ref _0, ref _1) => {
                                fmt.debug_tuple("View::__Ignore")
                                    .field(&_0)
                                    .field(&_1)
                                    .finish()
                            }
                        }
                    }
                }
            };
            const _: () = {
                impl<Runtime: Pip42> core::clone::Clone for View<Runtime> {
                    fn clone(&self) -> Self {
                        match self {
                            Self::__Ignore(ref _0, ref _1) => {
                                Self::__Ignore(
                                    core::clone::Clone::clone(_0),
                                    core::clone::Clone::clone(_1),
                                )
                            }
                        }
                    }
                }
            };
            const _: () = {
                impl<Runtime: Pip42> core::cmp::Eq for View<Runtime> {}
            };
            const _: () = {
                impl<Runtime: Pip42> core::cmp::PartialEq for View<Runtime> {
                    fn eq(&self, other: &Self) -> bool {
                        match (self, other) {
                            (
                                Self::__Ignore(_0, _1),
                                Self::__Ignore(_0_other, _1_other),
                            ) => true && _0 == _0_other && _1 == _1_other,
                        }
                    }
                }
            };
            #[allow(deprecated)]
            const _: () = {
                #[allow(non_camel_case_types)]
                #[automatically_derived]
                impl<Runtime: Pip42> ::codec::Encode for View<Runtime> {}
                #[automatically_derived]
                impl<Runtime: Pip42> ::codec::EncodeLike for View<Runtime> {}
            };
            #[allow(deprecated)]
            const _: () = {
                #[allow(non_camel_case_types)]
                #[automatically_derived]
                impl<Runtime: Pip42> ::codec::Decode for View<Runtime> {
                    fn decode<__CodecInputEdqy: ::codec::Input>(
                        __codec_input_edqy: &mut __CodecInputEdqy,
                    ) -> ::core::result::Result<Self, ::codec::Error> {
                        match __codec_input_edqy
                            .read_byte()
                            .map_err(|e| {
                                e
                                    .chain(
                                        "Could not decode `View`, failed to read variant byte",
                                    )
                            })?
                        {
                            _ => {
                                ::core::result::Result::Err(
                                    <_ as ::core::convert::Into<
                                        _,
                                    >>::into("Could not decode `View`, variant doesn't exist"),
                                )
                            }
                        }
                    }
                }
            };
            #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
            const _: () = {
                impl<Runtime: Pip42> ::scale_info::TypeInfo for View<Runtime>
                where
                    frame_support::sp_std::marker::PhantomData<
                        (Runtime),
                    >: ::scale_info::TypeInfo + 'static,
                    Runtime: Pip42 + 'static,
                {
                    type Identity = Self;
                    fn type_info() -> ::scale_info::Type {
                        ::scale_info::Type::builder()
                            .path(
                                ::scale_info::Path::new(
                                    "View",
                                    "pallet_interface::mock::interfaces::pip42",
                                ),
                            )
                            .type_params(
                                <[_]>::into_vec(
                                    #[rustc_box]
                                    ::alloc::boxed::Box::new([
                                        ::scale_info::TypeParameter::new(
                                            "Runtime",
                                            ::core::option::Option::None,
                                        ),
                                    ]),
                                ),
                            )
                            .variant(::scale_info::build::Variants::new())
                    }
                }
            };
            impl<Runtime: Pip42> View<Runtime> {}
            impl<Runtime: Pip42> frame_support::interface::View for View<Runtime> {
                fn view(self) -> frame_support::interface::ViewResult<Vec<u8>> {
                    match self {
                        Self::__Ignore(_, _) => {
                            {
                                ::core::panicking::panic_fmt(
                                    format_args!(
                                        "internal error: entered unreachable code: {0}",
                                        format_args!("__PhantomItem cannot be used.")
                                    ),
                                );
                            };
                        }
                    }
                }
            }
            impl<Runtime: Pip42> View<Runtime> {
                #[doc(hidden)]
                pub fn call_functions() -> frame_support::metadata::PalletCallMetadata {
                    frame_support::scale_info::meta_type::<View<Runtime>>().into()
                }
            }
        }
    }
    #[doc(hidden)]
    mod sp_api_hidden_includes_construct_runtime {
        pub extern crate frame_support as hidden_include;
    }
    const _: () = {
        #[allow(unused)]
        type __hidden_use_of_unchecked_extrinsic = UncheckedExtrinsic;
    };
    pub struct MockRuntime;
    #[automatically_derived]
    impl ::core::clone::Clone for MockRuntime {
        #[inline]
        fn clone(&self) -> MockRuntime {
            *self
        }
    }
    #[automatically_derived]
    impl ::core::marker::Copy for MockRuntime {}
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for MockRuntime {}
    #[automatically_derived]
    impl ::core::cmp::PartialEq for MockRuntime {
        #[inline]
        fn eq(&self, other: &MockRuntime) -> bool {
            true
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralEq for MockRuntime {}
    #[automatically_derived]
    impl ::core::cmp::Eq for MockRuntime {
        #[inline]
        #[doc(hidden)]
        #[no_coverage]
        fn assert_receiver_is_total_eq(&self) -> () {}
    }
    impl core::fmt::Debug for MockRuntime {
        fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
            fmt.debug_tuple("MockRuntime").finish()
        }
    }
    #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
    const _: () = {
        impl ::scale_info::TypeInfo for MockRuntime {
            type Identity = Self;
            fn type_info() -> ::scale_info::Type {
                ::scale_info::Type::builder()
                    .path(
                        ::scale_info::Path::new("MockRuntime", "pallet_interface::mock"),
                    )
                    .type_params(::alloc::vec::Vec::new())
                    .composite(::scale_info::build::Fields::unit())
            }
        }
    };
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_runtime::traits::GetNodeBlockType
    for MockRuntime {
        type NodeBlock = Block;
    }
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_runtime::traits::GetRuntimeBlockType
    for MockRuntime {
        type RuntimeBlock = Block;
    }
    #[allow(non_camel_case_types)]
    pub enum RuntimeEvent {
        #[codec(index = 0u8)]
        System(frame_system::Event<MockRuntime>),
        #[codec(index = 1u8)]
        Balances(pallet_balances::Event<MockRuntime>),
    }
    #[automatically_derived]
    #[allow(non_camel_case_types)]
    impl ::core::clone::Clone for RuntimeEvent {
        #[inline]
        fn clone(&self) -> RuntimeEvent {
            match self {
                RuntimeEvent::System(__self_0) => {
                    RuntimeEvent::System(::core::clone::Clone::clone(__self_0))
                }
                RuntimeEvent::Balances(__self_0) => {
                    RuntimeEvent::Balances(::core::clone::Clone::clone(__self_0))
                }
            }
        }
    }
    #[allow(non_camel_case_types)]
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for RuntimeEvent {}
    #[automatically_derived]
    #[allow(non_camel_case_types)]
    impl ::core::cmp::PartialEq for RuntimeEvent {
        #[inline]
        fn eq(&self, other: &RuntimeEvent) -> bool {
            let __self_tag = ::core::intrinsics::discriminant_value(self);
            let __arg1_tag = ::core::intrinsics::discriminant_value(other);
            __self_tag == __arg1_tag
                && match (self, other) {
                    (RuntimeEvent::System(__self_0), RuntimeEvent::System(__arg1_0)) => {
                        *__self_0 == *__arg1_0
                    }
                    (
                        RuntimeEvent::Balances(__self_0),
                        RuntimeEvent::Balances(__arg1_0),
                    ) => *__self_0 == *__arg1_0,
                    _ => unsafe { ::core::intrinsics::unreachable() }
                }
        }
    }
    #[allow(non_camel_case_types)]
    #[automatically_derived]
    impl ::core::marker::StructuralEq for RuntimeEvent {}
    #[automatically_derived]
    #[allow(non_camel_case_types)]
    impl ::core::cmp::Eq for RuntimeEvent {
        #[inline]
        #[doc(hidden)]
        #[no_coverage]
        fn assert_receiver_is_total_eq(&self) -> () {
            let _: ::core::cmp::AssertParamIsEq<frame_system::Event<MockRuntime>>;
            let _: ::core::cmp::AssertParamIsEq<pallet_balances::Event<MockRuntime>>;
        }
    }
    #[allow(deprecated)]
    const _: () = {
        #[allow(non_camel_case_types)]
        #[automatically_derived]
        impl ::codec::Encode for RuntimeEvent {
            fn encode_to<__CodecOutputEdqy: ::codec::Output + ?::core::marker::Sized>(
                &self,
                __codec_dest_edqy: &mut __CodecOutputEdqy,
            ) {
                match *self {
                    RuntimeEvent::System(ref aa) => {
                        __codec_dest_edqy.push_byte(0u8 as ::core::primitive::u8);
                        ::codec::Encode::encode_to(aa, __codec_dest_edqy);
                    }
                    RuntimeEvent::Balances(ref aa) => {
                        __codec_dest_edqy.push_byte(1u8 as ::core::primitive::u8);
                        ::codec::Encode::encode_to(aa, __codec_dest_edqy);
                    }
                    _ => {}
                }
            }
        }
        #[automatically_derived]
        impl ::codec::EncodeLike for RuntimeEvent {}
    };
    #[allow(deprecated)]
    const _: () = {
        #[allow(non_camel_case_types)]
        #[automatically_derived]
        impl ::codec::Decode for RuntimeEvent {
            fn decode<__CodecInputEdqy: ::codec::Input>(
                __codec_input_edqy: &mut __CodecInputEdqy,
            ) -> ::core::result::Result<Self, ::codec::Error> {
                match __codec_input_edqy
                    .read_byte()
                    .map_err(|e| {
                        e
                            .chain(
                                "Could not decode `RuntimeEvent`, failed to read variant byte",
                            )
                    })?
                {
                    __codec_x_edqy if __codec_x_edqy == 0u8 as ::core::primitive::u8 => {
                        ::core::result::Result::Ok(
                            RuntimeEvent::System({
                                let __codec_res_edqy = <frame_system::Event<
                                    MockRuntime,
                                > as ::codec::Decode>::decode(__codec_input_edqy);
                                match __codec_res_edqy {
                                    ::core::result::Result::Err(e) => {
                                        return ::core::result::Result::Err(
                                            e.chain("Could not decode `RuntimeEvent::System.0`"),
                                        );
                                    }
                                    ::core::result::Result::Ok(__codec_res_edqy) => {
                                        __codec_res_edqy
                                    }
                                }
                            }),
                        )
                    }
                    __codec_x_edqy if __codec_x_edqy == 1u8 as ::core::primitive::u8 => {
                        ::core::result::Result::Ok(
                            RuntimeEvent::Balances({
                                let __codec_res_edqy = <pallet_balances::Event<
                                    MockRuntime,
                                > as ::codec::Decode>::decode(__codec_input_edqy);
                                match __codec_res_edqy {
                                    ::core::result::Result::Err(e) => {
                                        return ::core::result::Result::Err(
                                            e.chain("Could not decode `RuntimeEvent::Balances.0`"),
                                        );
                                    }
                                    ::core::result::Result::Ok(__codec_res_edqy) => {
                                        __codec_res_edqy
                                    }
                                }
                            }),
                        )
                    }
                    _ => {
                        ::core::result::Result::Err(
                            <_ as ::core::convert::Into<
                                _,
                            >>::into(
                                "Could not decode `RuntimeEvent`, variant doesn't exist",
                            ),
                        )
                    }
                }
            }
        }
    };
    #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
    const _: () = {
        impl ::scale_info::TypeInfo for RuntimeEvent {
            type Identity = Self;
            fn type_info() -> ::scale_info::Type {
                ::scale_info::Type::builder()
                    .path(
                        ::scale_info::Path::new("RuntimeEvent", "pallet_interface::mock"),
                    )
                    .type_params(::alloc::vec::Vec::new())
                    .variant(
                        ::scale_info::build::Variants::new()
                            .variant(
                                "System",
                                |v| {
                                    v
                                        .index(0u8 as ::core::primitive::u8)
                                        .fields(
                                            ::scale_info::build::Fields::unnamed()
                                                .field(|f| {
                                                    f
                                                        .ty::<frame_system::Event<MockRuntime>>()
                                                        .type_name("frame_system::Event<MockRuntime>")
                                                }),
                                        )
                                },
                            )
                            .variant(
                                "Balances",
                                |v| {
                                    v
                                        .index(1u8 as ::core::primitive::u8)
                                        .fields(
                                            ::scale_info::build::Fields::unnamed()
                                                .field(|f| {
                                                    f
                                                        .ty::<pallet_balances::Event<MockRuntime>>()
                                                        .type_name("pallet_balances::Event<MockRuntime>")
                                                }),
                                        )
                                },
                            ),
                    )
            }
        }
    };
    impl core::fmt::Debug for RuntimeEvent {
        fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
            match self {
                Self::System(ref a0) => {
                    fmt.debug_tuple("RuntimeEvent::System").field(a0).finish()
                }
                Self::Balances(ref a0) => {
                    fmt.debug_tuple("RuntimeEvent::Balances").field(a0).finish()
                }
                _ => Ok(()),
            }
        }
    }
    impl From<frame_system::Event<MockRuntime>> for RuntimeEvent {
        fn from(x: frame_system::Event<MockRuntime>) -> Self {
            RuntimeEvent::System(x)
        }
    }
    impl TryInto<frame_system::Event<MockRuntime>> for RuntimeEvent {
        type Error = ();
        fn try_into(
            self,
        ) -> self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::result::Result<
            frame_system::Event<MockRuntime>,
            Self::Error,
        > {
            match self {
                Self::System(evt) => Ok(evt),
                _ => Err(()),
            }
        }
    }
    impl From<pallet_balances::Event<MockRuntime>> for RuntimeEvent {
        fn from(x: pallet_balances::Event<MockRuntime>) -> Self {
            RuntimeEvent::Balances(x)
        }
    }
    impl TryInto<pallet_balances::Event<MockRuntime>> for RuntimeEvent {
        type Error = ();
        fn try_into(
            self,
        ) -> self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::result::Result<
            pallet_balances::Event<MockRuntime>,
            Self::Error,
        > {
            match self {
                Self::Balances(evt) => Ok(evt),
                _ => Err(()),
            }
        }
    }
    /// The runtime origin type representing the origin of a call.
    ///
    /// Origin is always created with the base filter configured in [`frame_system::Config::BaseCallFilter`].
    pub struct RuntimeOrigin {
        caller: OriginCaller,
        filter: self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::rc::Rc<
            Box<dyn Fn(&<MockRuntime as frame_system::Config>::RuntimeCall) -> bool>,
        >,
    }
    #[automatically_derived]
    impl ::core::clone::Clone for RuntimeOrigin {
        #[inline]
        fn clone(&self) -> RuntimeOrigin {
            RuntimeOrigin {
                caller: ::core::clone::Clone::clone(&self.caller),
                filter: ::core::clone::Clone::clone(&self.filter),
            }
        }
    }
    #[cfg(feature = "std")]
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::fmt::Debug
    for RuntimeOrigin {
        fn fmt(
            &self,
            fmt: &mut self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::fmt::Formatter,
        ) -> self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::result::Result<
            (),
            self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::fmt::Error,
        > {
            fmt.debug_struct("Origin")
                .field("caller", &self.caller)
                .field("filter", &"[function ptr]")
                .finish()
        }
    }
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::OriginTrait
    for RuntimeOrigin {
        type Call = <MockRuntime as frame_system::Config>::RuntimeCall;
        type PalletsOrigin = OriginCaller;
        type AccountId = <MockRuntime as frame_system::Config>::AccountId;
        fn add_filter(&mut self, filter: impl Fn(&Self::Call) -> bool + 'static) {
            let f = self.filter.clone();
            self
                .filter = self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::rc::Rc::new(
                Box::new(move |call| { f(call) && filter(call) }),
            );
        }
        fn reset_filter(&mut self) {
            let filter = <<MockRuntime as frame_system::Config>::BaseCallFilter as self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::Contains<
                <MockRuntime as frame_system::Config>::RuntimeCall,
            >>::contains;
            self
                .filter = self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::rc::Rc::new(
                Box::new(filter),
            );
        }
        fn set_caller_from(&mut self, other: impl Into<Self>) {
            self.caller = other.into().caller;
        }
        fn filter_call(&self, call: &Self::Call) -> bool {
            match self.caller {
                OriginCaller::system(frame_system::Origin::<MockRuntime>::Root) => true,
                _ => (self.filter)(call),
            }
        }
        fn caller(&self) -> &Self::PalletsOrigin {
            &self.caller
        }
        fn into_caller(self) -> Self::PalletsOrigin {
            self.caller
        }
        fn try_with_caller<R>(
            mut self,
            f: impl FnOnce(Self::PalletsOrigin) -> Result<R, Self::PalletsOrigin>,
        ) -> Result<R, Self> {
            match f(self.caller) {
                Ok(r) => Ok(r),
                Err(caller) => {
                    self.caller = caller;
                    Err(self)
                }
            }
        }
        fn none() -> Self {
            frame_system::RawOrigin::None.into()
        }
        fn root() -> Self {
            frame_system::RawOrigin::Root.into()
        }
        fn signed(by: Self::AccountId) -> Self {
            frame_system::RawOrigin::Signed(by).into()
        }
    }
    #[allow(non_camel_case_types)]
    pub enum OriginCaller {
        #[codec(index = 0u8)]
        system(frame_system::Origin<MockRuntime>),
        #[allow(dead_code)]
        Void(self::sp_api_hidden_includes_construct_runtime::hidden_include::Void),
    }
    #[automatically_derived]
    #[allow(non_camel_case_types)]
    impl ::core::clone::Clone for OriginCaller {
        #[inline]
        fn clone(&self) -> OriginCaller {
            match self {
                OriginCaller::system(__self_0) => {
                    OriginCaller::system(::core::clone::Clone::clone(__self_0))
                }
                OriginCaller::Void(__self_0) => {
                    OriginCaller::Void(::core::clone::Clone::clone(__self_0))
                }
            }
        }
    }
    #[allow(non_camel_case_types)]
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for OriginCaller {}
    #[automatically_derived]
    #[allow(non_camel_case_types)]
    impl ::core::cmp::PartialEq for OriginCaller {
        #[inline]
        fn eq(&self, other: &OriginCaller) -> bool {
            let __self_tag = ::core::intrinsics::discriminant_value(self);
            let __arg1_tag = ::core::intrinsics::discriminant_value(other);
            __self_tag == __arg1_tag
                && match (self, other) {
                    (OriginCaller::system(__self_0), OriginCaller::system(__arg1_0)) => {
                        *__self_0 == *__arg1_0
                    }
                    (OriginCaller::Void(__self_0), OriginCaller::Void(__arg1_0)) => {
                        *__self_0 == *__arg1_0
                    }
                    _ => unsafe { ::core::intrinsics::unreachable() }
                }
        }
    }
    #[allow(non_camel_case_types)]
    #[automatically_derived]
    impl ::core::marker::StructuralEq for OriginCaller {}
    #[automatically_derived]
    #[allow(non_camel_case_types)]
    impl ::core::cmp::Eq for OriginCaller {
        #[inline]
        #[doc(hidden)]
        #[no_coverage]
        fn assert_receiver_is_total_eq(&self) -> () {
            let _: ::core::cmp::AssertParamIsEq<frame_system::Origin<MockRuntime>>;
            let _: ::core::cmp::AssertParamIsEq<
                self::sp_api_hidden_includes_construct_runtime::hidden_include::Void,
            >;
        }
    }
    impl core::fmt::Debug for OriginCaller {
        fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
            match self {
                Self::system(ref a0) => {
                    fmt.debug_tuple("OriginCaller::system").field(a0).finish()
                }
                Self::Void(ref a0) => {
                    fmt.debug_tuple("OriginCaller::Void").field(a0).finish()
                }
                _ => Ok(()),
            }
        }
    }
    #[allow(deprecated)]
    const _: () = {
        #[allow(non_camel_case_types)]
        #[automatically_derived]
        impl ::codec::Encode for OriginCaller {
            fn encode_to<__CodecOutputEdqy: ::codec::Output + ?::core::marker::Sized>(
                &self,
                __codec_dest_edqy: &mut __CodecOutputEdqy,
            ) {
                match *self {
                    OriginCaller::system(ref aa) => {
                        __codec_dest_edqy.push_byte(0u8 as ::core::primitive::u8);
                        ::codec::Encode::encode_to(aa, __codec_dest_edqy);
                    }
                    OriginCaller::Void(ref aa) => {
                        __codec_dest_edqy.push_byte(1usize as ::core::primitive::u8);
                        ::codec::Encode::encode_to(aa, __codec_dest_edqy);
                    }
                    _ => {}
                }
            }
        }
        #[automatically_derived]
        impl ::codec::EncodeLike for OriginCaller {}
    };
    #[allow(deprecated)]
    const _: () = {
        #[allow(non_camel_case_types)]
        #[automatically_derived]
        impl ::codec::Decode for OriginCaller {
            fn decode<__CodecInputEdqy: ::codec::Input>(
                __codec_input_edqy: &mut __CodecInputEdqy,
            ) -> ::core::result::Result<Self, ::codec::Error> {
                match __codec_input_edqy
                    .read_byte()
                    .map_err(|e| {
                        e
                            .chain(
                                "Could not decode `OriginCaller`, failed to read variant byte",
                            )
                    })?
                {
                    __codec_x_edqy if __codec_x_edqy == 0u8 as ::core::primitive::u8 => {
                        ::core::result::Result::Ok(
                            OriginCaller::system({
                                let __codec_res_edqy = <frame_system::Origin<
                                    MockRuntime,
                                > as ::codec::Decode>::decode(__codec_input_edqy);
                                match __codec_res_edqy {
                                    ::core::result::Result::Err(e) => {
                                        return ::core::result::Result::Err(
                                            e.chain("Could not decode `OriginCaller::system.0`"),
                                        );
                                    }
                                    ::core::result::Result::Ok(__codec_res_edqy) => {
                                        __codec_res_edqy
                                    }
                                }
                            }),
                        )
                    }
                    __codec_x_edqy if __codec_x_edqy
                        == 1usize as ::core::primitive::u8 => {
                        ::core::result::Result::Ok(
                            OriginCaller::Void({
                                let __codec_res_edqy = <self::sp_api_hidden_includes_construct_runtime::hidden_include::Void as ::codec::Decode>::decode(
                                    __codec_input_edqy,
                                );
                                match __codec_res_edqy {
                                    ::core::result::Result::Err(e) => {
                                        return ::core::result::Result::Err(
                                            e.chain("Could not decode `OriginCaller::Void.0`"),
                                        );
                                    }
                                    ::core::result::Result::Ok(__codec_res_edqy) => {
                                        __codec_res_edqy
                                    }
                                }
                            }),
                        )
                    }
                    _ => {
                        ::core::result::Result::Err(
                            <_ as ::core::convert::Into<
                                _,
                            >>::into(
                                "Could not decode `OriginCaller`, variant doesn't exist",
                            ),
                        )
                    }
                }
            }
        }
    };
    #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
    const _: () = {
        impl ::scale_info::TypeInfo for OriginCaller {
            type Identity = Self;
            fn type_info() -> ::scale_info::Type {
                ::scale_info::Type::builder()
                    .path(
                        ::scale_info::Path::new("OriginCaller", "pallet_interface::mock"),
                    )
                    .type_params(::alloc::vec::Vec::new())
                    .variant(
                        ::scale_info::build::Variants::new()
                            .variant(
                                "system",
                                |v| {
                                    v
                                        .index(0u8 as ::core::primitive::u8)
                                        .fields(
                                            ::scale_info::build::Fields::unnamed()
                                                .field(|f| {
                                                    f
                                                        .ty::<frame_system::Origin<MockRuntime>>()
                                                        .type_name("frame_system::Origin<MockRuntime>")
                                                }),
                                        )
                                },
                            )
                            .variant(
                                "Void",
                                |v| {
                                    v
                                        .index(1usize as ::core::primitive::u8)
                                        .fields(
                                            ::scale_info::build::Fields::unnamed()
                                                .field(|f| {
                                                    f
                                                        .ty::<
                                                            self::sp_api_hidden_includes_construct_runtime::hidden_include::Void,
                                                        >()
                                                        .type_name(
                                                            "self::sp_api_hidden_includes_construct_runtime::hidden_include::Void",
                                                        )
                                                }),
                                        )
                                },
                            ),
                    )
            }
        }
    };
    const _: () = {
        impl ::codec::MaxEncodedLen for OriginCaller {
            fn max_encoded_len() -> ::core::primitive::usize {
                0_usize
                    .max(
                        0_usize
                            .saturating_add(
                                <frame_system::Origin<MockRuntime>>::max_encoded_len(),
                            ),
                    )
                    .max(
                        0_usize
                            .saturating_add(
                                <self::sp_api_hidden_includes_construct_runtime::hidden_include::Void>::max_encoded_len(),
                            ),
                    )
                    .saturating_add(1)
            }
        }
    };
    #[allow(dead_code)]
    impl RuntimeOrigin {
        /// Create with system none origin and [`frame_system::Config::BaseCallFilter`].
        pub fn none() -> Self {
            <RuntimeOrigin as self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::OriginTrait>::none()
        }
        /// Create with system root origin and [`frame_system::Config::BaseCallFilter`].
        pub fn root() -> Self {
            <RuntimeOrigin as self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::OriginTrait>::root()
        }
        /// Create with system signed origin and [`frame_system::Config::BaseCallFilter`].
        pub fn signed(by: <MockRuntime as frame_system::Config>::AccountId) -> Self {
            <RuntimeOrigin as self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::OriginTrait>::signed(
                by,
            )
        }
    }
    impl From<frame_system::Origin<MockRuntime>> for OriginCaller {
        fn from(x: frame_system::Origin<MockRuntime>) -> Self {
            OriginCaller::system(x)
        }
    }
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::CallerTrait<
        <MockRuntime as frame_system::Config>::AccountId,
    > for OriginCaller {
        fn into_system(
            self,
        ) -> Option<
            frame_system::RawOrigin<<MockRuntime as frame_system::Config>::AccountId>,
        > {
            match self {
                OriginCaller::system(x) => Some(x),
                _ => None,
            }
        }
        fn as_system_ref(
            &self,
        ) -> Option<
            &frame_system::RawOrigin<<MockRuntime as frame_system::Config>::AccountId>,
        > {
            match &self {
                OriginCaller::system(o) => Some(o),
                _ => None,
            }
        }
    }
    impl TryFrom<OriginCaller> for frame_system::Origin<MockRuntime> {
        type Error = OriginCaller;
        fn try_from(
            x: OriginCaller,
        ) -> self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::result::Result<
            frame_system::Origin<MockRuntime>,
            OriginCaller,
        > {
            if let OriginCaller::system(l) = x { Ok(l) } else { Err(x) }
        }
    }
    impl From<frame_system::Origin<MockRuntime>> for RuntimeOrigin {
        /// Convert to runtime origin, using as filter: [`frame_system::Config::BaseCallFilter`].
        fn from(x: frame_system::Origin<MockRuntime>) -> Self {
            let o: OriginCaller = x.into();
            o.into()
        }
    }
    impl From<OriginCaller> for RuntimeOrigin {
        fn from(x: OriginCaller) -> Self {
            let mut o = RuntimeOrigin {
                caller: x,
                filter: self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::rc::Rc::new(
                    Box::new(|_| true),
                ),
            };
            self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::OriginTrait::reset_filter(
                &mut o,
            );
            o
        }
    }
    impl From<RuntimeOrigin>
    for self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::result::Result<
        frame_system::Origin<MockRuntime>,
        RuntimeOrigin,
    > {
        /// NOTE: converting to pallet origin loses the origin filter information.
        fn from(val: RuntimeOrigin) -> Self {
            if let OriginCaller::system(l) = val.caller { Ok(l) } else { Err(val) }
        }
    }
    impl From<Option<<MockRuntime as frame_system::Config>::AccountId>>
    for RuntimeOrigin {
        /// Convert to runtime origin with caller being system signed or none and use filter [`frame_system::Config::BaseCallFilter`].
        fn from(x: Option<<MockRuntime as frame_system::Config>::AccountId>) -> Self {
            <frame_system::Origin<MockRuntime>>::from(x).into()
        }
    }
    pub type System = frame_system::Pallet<MockRuntime>;
    pub type Balances = pallet_balances::Pallet<MockRuntime>;
    pub type Interface = pallet_interface::Pallet<MockRuntime>;
    /// All pallets included in the runtime as a nested tuple of types.
    #[deprecated(
        note = "The type definition has changed from representing all pallets \
			excluding system, in reversed order to become the representation of all pallets \
			including system pallet in regular order. For this reason it is encouraged to use \
			explicitly one of `AllPalletsWithSystem`, `AllPalletsWithoutSystem`, \
			`AllPalletsWithSystemReversed`, `AllPalletsWithoutSystemReversed`. \
			Note that the type `frame_executive::Executive` expects one of `AllPalletsWithSystem` \
			, `AllPalletsWithSystemReversed`, `AllPalletsReversedWithSystemFirst`. More details in \
			https://github.com/paritytech/substrate/pull/10043"
    )]
    pub type AllPallets = AllPalletsWithSystem;
    #[cfg(all())]
    /// All pallets included in the runtime as a nested tuple of types.
    pub type AllPalletsWithSystem = (System, Balances, Interface);
    #[cfg(all())]
    /// All pallets included in the runtime as a nested tuple of types.
    /// Excludes the System pallet.
    pub type AllPalletsWithoutSystem = (Balances, Interface);
    #[cfg(all())]
    /// All pallets included in the runtime as a nested tuple of types in reversed order.
    #[deprecated(
        note = "Using reverse pallet orders is deprecated. use only \
			`AllPalletsWithSystem or AllPalletsWithoutSystem`"
    )]
    pub type AllPalletsWithSystemReversed = (Interface, Balances, System);
    #[cfg(all())]
    /// All pallets included in the runtime as a nested tuple of types in reversed order.
    /// Excludes the System pallet.
    #[deprecated(
        note = "Using reverse pallet orders is deprecated. use only \
			`AllPalletsWithSystem or AllPalletsWithoutSystem`"
    )]
    pub type AllPalletsWithoutSystemReversed = (Interface, Balances);
    #[cfg(all())]
    /// All pallets included in the runtime as a nested tuple of types in reversed order.
    /// With the system pallet first.
    #[deprecated(
        note = "Using reverse pallet orders is deprecated. use only \
			`AllPalletsWithSystem or AllPalletsWithoutSystem`"
    )]
    pub type AllPalletsReversedWithSystemFirst = (System, Interface, Balances);
    /// Provides an implementation of `PalletInfo` to provide information
    /// about the pallet setup in the runtime.
    pub struct PalletInfo;
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::PalletInfo
    for PalletInfo {
        fn index<P: 'static>() -> Option<usize> {
            let type_id = self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                P,
            >();
            if type_id
                == self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                    System,
                >()
            {
                return Some(0usize);
            }
            if type_id
                == self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                    Balances,
                >()
            {
                return Some(1usize);
            }
            if type_id
                == self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                    Interface,
                >()
            {
                return Some(255usize);
            }
            None
        }
        fn name<P: 'static>() -> Option<&'static str> {
            let type_id = self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                P,
            >();
            if type_id
                == self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                    System,
                >()
            {
                return Some("System");
            }
            if type_id
                == self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                    Balances,
                >()
            {
                return Some("Balances");
            }
            if type_id
                == self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                    Interface,
                >()
            {
                return Some("Interface");
            }
            None
        }
        fn module_name<P: 'static>() -> Option<&'static str> {
            let type_id = self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                P,
            >();
            if type_id
                == self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                    System,
                >()
            {
                return Some("frame_system");
            }
            if type_id
                == self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                    Balances,
                >()
            {
                return Some("pallet_balances");
            }
            if type_id
                == self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                    Interface,
                >()
            {
                return Some("pallet_interface");
            }
            None
        }
        fn crate_version<P: 'static>() -> Option<
            self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::CrateVersion,
        > {
            let type_id = self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                P,
            >();
            if type_id
                == self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                    System,
                >()
            {
                return Some(
                    <frame_system::Pallet<
                        MockRuntime,
                    > as self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::PalletInfoAccess>::crate_version(),
                );
            }
            if type_id
                == self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                    Balances,
                >()
            {
                return Some(
                    <pallet_balances::Pallet<
                        MockRuntime,
                    > as self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::PalletInfoAccess>::crate_version(),
                );
            }
            if type_id
                == self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::any::TypeId::of::<
                    Interface,
                >()
            {
                return Some(
                    <pallet_interface::Pallet<
                        MockRuntime,
                    > as self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::PalletInfoAccess>::crate_version(),
                );
            }
            None
        }
    }
    pub enum RuntimeCall {
        #[codec(index = 0u8)]
        System(
            self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                System,
                MockRuntime,
            >,
        ),
        #[codec(index = 1u8)]
        Balances(
            self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                Balances,
                MockRuntime,
            >,
        ),
        #[codec(index = 255u8)]
        Interface(
            self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                Interface,
                MockRuntime,
            >,
        ),
    }
    #[automatically_derived]
    impl ::core::clone::Clone for RuntimeCall {
        #[inline]
        fn clone(&self) -> RuntimeCall {
            match self {
                RuntimeCall::System(__self_0) => {
                    RuntimeCall::System(::core::clone::Clone::clone(__self_0))
                }
                RuntimeCall::Balances(__self_0) => {
                    RuntimeCall::Balances(::core::clone::Clone::clone(__self_0))
                }
                RuntimeCall::Interface(__self_0) => {
                    RuntimeCall::Interface(::core::clone::Clone::clone(__self_0))
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for RuntimeCall {}
    #[automatically_derived]
    impl ::core::cmp::PartialEq for RuntimeCall {
        #[inline]
        fn eq(&self, other: &RuntimeCall) -> bool {
            let __self_tag = ::core::intrinsics::discriminant_value(self);
            let __arg1_tag = ::core::intrinsics::discriminant_value(other);
            __self_tag == __arg1_tag
                && match (self, other) {
                    (RuntimeCall::System(__self_0), RuntimeCall::System(__arg1_0)) => {
                        *__self_0 == *__arg1_0
                    }
                    (
                        RuntimeCall::Balances(__self_0),
                        RuntimeCall::Balances(__arg1_0),
                    ) => *__self_0 == *__arg1_0,
                    (
                        RuntimeCall::Interface(__self_0),
                        RuntimeCall::Interface(__arg1_0),
                    ) => *__self_0 == *__arg1_0,
                    _ => unsafe { ::core::intrinsics::unreachable() }
                }
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralEq for RuntimeCall {}
    #[automatically_derived]
    impl ::core::cmp::Eq for RuntimeCall {
        #[inline]
        #[doc(hidden)]
        #[no_coverage]
        fn assert_receiver_is_total_eq(&self) -> () {
            let _: ::core::cmp::AssertParamIsEq<
                self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                    System,
                    MockRuntime,
                >,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                    Balances,
                    MockRuntime,
                >,
            >;
            let _: ::core::cmp::AssertParamIsEq<
                self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                    Interface,
                    MockRuntime,
                >,
            >;
        }
    }
    #[allow(deprecated)]
    const _: () = {
        #[automatically_derived]
        impl ::codec::Encode for RuntimeCall {
            fn encode_to<__CodecOutputEdqy: ::codec::Output + ?::core::marker::Sized>(
                &self,
                __codec_dest_edqy: &mut __CodecOutputEdqy,
            ) {
                match *self {
                    RuntimeCall::System(ref aa) => {
                        __codec_dest_edqy.push_byte(0u8 as ::core::primitive::u8);
                        ::codec::Encode::encode_to(aa, __codec_dest_edqy);
                    }
                    RuntimeCall::Balances(ref aa) => {
                        __codec_dest_edqy.push_byte(1u8 as ::core::primitive::u8);
                        ::codec::Encode::encode_to(aa, __codec_dest_edqy);
                    }
                    RuntimeCall::Interface(ref aa) => {
                        __codec_dest_edqy.push_byte(255u8 as ::core::primitive::u8);
                        ::codec::Encode::encode_to(aa, __codec_dest_edqy);
                    }
                    _ => {}
                }
            }
        }
        #[automatically_derived]
        impl ::codec::EncodeLike for RuntimeCall {}
    };
    #[allow(deprecated)]
    const _: () = {
        #[automatically_derived]
        impl ::codec::Decode for RuntimeCall {
            fn decode<__CodecInputEdqy: ::codec::Input>(
                __codec_input_edqy: &mut __CodecInputEdqy,
            ) -> ::core::result::Result<Self, ::codec::Error> {
                match __codec_input_edqy
                    .read_byte()
                    .map_err(|e| {
                        e
                            .chain(
                                "Could not decode `RuntimeCall`, failed to read variant byte",
                            )
                    })?
                {
                    __codec_x_edqy if __codec_x_edqy == 0u8 as ::core::primitive::u8 => {
                        ::core::result::Result::Ok(
                            RuntimeCall::System({
                                let __codec_res_edqy = <self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                                    System,
                                    MockRuntime,
                                > as ::codec::Decode>::decode(__codec_input_edqy);
                                match __codec_res_edqy {
                                    ::core::result::Result::Err(e) => {
                                        return ::core::result::Result::Err(
                                            e.chain("Could not decode `RuntimeCall::System.0`"),
                                        );
                                    }
                                    ::core::result::Result::Ok(__codec_res_edqy) => {
                                        __codec_res_edqy
                                    }
                                }
                            }),
                        )
                    }
                    __codec_x_edqy if __codec_x_edqy == 1u8 as ::core::primitive::u8 => {
                        ::core::result::Result::Ok(
                            RuntimeCall::Balances({
                                let __codec_res_edqy = <self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                                    Balances,
                                    MockRuntime,
                                > as ::codec::Decode>::decode(__codec_input_edqy);
                                match __codec_res_edqy {
                                    ::core::result::Result::Err(e) => {
                                        return ::core::result::Result::Err(
                                            e.chain("Could not decode `RuntimeCall::Balances.0`"),
                                        );
                                    }
                                    ::core::result::Result::Ok(__codec_res_edqy) => {
                                        __codec_res_edqy
                                    }
                                }
                            }),
                        )
                    }
                    __codec_x_edqy if __codec_x_edqy
                        == 255u8 as ::core::primitive::u8 => {
                        ::core::result::Result::Ok(
                            RuntimeCall::Interface({
                                let __codec_res_edqy = <self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                                    Interface,
                                    MockRuntime,
                                > as ::codec::Decode>::decode(__codec_input_edqy);
                                match __codec_res_edqy {
                                    ::core::result::Result::Err(e) => {
                                        return ::core::result::Result::Err(
                                            e.chain("Could not decode `RuntimeCall::Interface.0`"),
                                        );
                                    }
                                    ::core::result::Result::Ok(__codec_res_edqy) => {
                                        __codec_res_edqy
                                    }
                                }
                            }),
                        )
                    }
                    _ => {
                        ::core::result::Result::Err(
                            <_ as ::core::convert::Into<
                                _,
                            >>::into(
                                "Could not decode `RuntimeCall`, variant doesn't exist",
                            ),
                        )
                    }
                }
            }
        }
    };
    #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
    const _: () = {
        impl ::scale_info::TypeInfo for RuntimeCall {
            type Identity = Self;
            fn type_info() -> ::scale_info::Type {
                ::scale_info::Type::builder()
                    .path(
                        ::scale_info::Path::new("RuntimeCall", "pallet_interface::mock"),
                    )
                    .type_params(::alloc::vec::Vec::new())
                    .variant(
                        ::scale_info::build::Variants::new()
                            .variant(
                                "System",
                                |v| {
                                    v
                                        .index(0u8 as ::core::primitive::u8)
                                        .fields(
                                            ::scale_info::build::Fields::unnamed()
                                                .field(|f| {
                                                    f
                                                        .ty::<
                                                            self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                                                                System,
                                                                MockRuntime,
                                                            >,
                                                        >()
                                                        .type_name(
                                                            "self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch\n::CallableCallFor<System, MockRuntime>",
                                                        )
                                                }),
                                        )
                                },
                            )
                            .variant(
                                "Balances",
                                |v| {
                                    v
                                        .index(1u8 as ::core::primitive::u8)
                                        .fields(
                                            ::scale_info::build::Fields::unnamed()
                                                .field(|f| {
                                                    f
                                                        .ty::<
                                                            self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                                                                Balances,
                                                                MockRuntime,
                                                            >,
                                                        >()
                                                        .type_name(
                                                            "self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch\n::CallableCallFor<Balances, MockRuntime>",
                                                        )
                                                }),
                                        )
                                },
                            )
                            .variant(
                                "Interface",
                                |v| {
                                    v
                                        .index(255u8 as ::core::primitive::u8)
                                        .fields(
                                            ::scale_info::build::Fields::unnamed()
                                                .field(|f| {
                                                    f
                                                        .ty::<
                                                            self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                                                                Interface,
                                                                MockRuntime,
                                                            >,
                                                        >()
                                                        .type_name(
                                                            "self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch\n::CallableCallFor<Interface, MockRuntime>",
                                                        )
                                                }),
                                        )
                                },
                            ),
                    )
            }
        }
    };
    impl core::fmt::Debug for RuntimeCall {
        fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
            match self {
                Self::System(ref a0) => {
                    fmt.debug_tuple("RuntimeCall::System").field(a0).finish()
                }
                Self::Balances(ref a0) => {
                    fmt.debug_tuple("RuntimeCall::Balances").field(a0).finish()
                }
                Self::Interface(ref a0) => {
                    fmt.debug_tuple("RuntimeCall::Interface").field(a0).finish()
                }
                _ => Ok(()),
            }
        }
    }
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::GetDispatchInfo
    for RuntimeCall {
        fn get_dispatch_info(
            &self,
        ) -> self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::DispatchInfo {
            match self {
                RuntimeCall::System(call) => call.get_dispatch_info(),
                RuntimeCall::Balances(call) => call.get_dispatch_info(),
                RuntimeCall::Interface(call) => call.get_dispatch_info(),
            }
        }
    }
    #[allow(deprecated)]
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::weights::GetDispatchInfo
    for RuntimeCall {}
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::GetCallMetadata
    for RuntimeCall {
        fn get_call_metadata(
            &self,
        ) -> self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallMetadata {
            use self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::GetCallName;
            match self {
                RuntimeCall::System(call) => {
                    let function_name = call.get_call_name();
                    let pallet_name = "System";
                    self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallMetadata {
                        function_name,
                        pallet_name,
                    }
                }
                RuntimeCall::Balances(call) => {
                    let function_name = call.get_call_name();
                    let pallet_name = "Balances";
                    self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallMetadata {
                        function_name,
                        pallet_name,
                    }
                }
                RuntimeCall::Interface(call) => {
                    let function_name = call.get_call_name();
                    let pallet_name = "Interface";
                    self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallMetadata {
                        function_name,
                        pallet_name,
                    }
                }
            }
        }
        fn get_module_names() -> &'static [&'static str] {
            &["System", "Balances", "Interface"]
        }
        fn get_call_names(module: &str) -> &'static [&'static str] {
            use self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::{
                Callable, GetCallName,
            };
            match module {
                "System" => {
                    <<System as Callable<
                        MockRuntime,
                    >>::RuntimeCall as GetCallName>::get_call_names()
                }
                "Balances" => {
                    <<Balances as Callable<
                        MockRuntime,
                    >>::RuntimeCall as GetCallName>::get_call_names()
                }
                "Interface" => {
                    <<Interface as Callable<
                        MockRuntime,
                    >>::RuntimeCall as GetCallName>::get_call_names()
                }
                _ => ::core::panicking::panic("internal error: entered unreachable code"),
            }
        }
    }
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::Dispatchable
    for RuntimeCall {
        type RuntimeOrigin = RuntimeOrigin;
        type Config = RuntimeCall;
        type Info = self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::DispatchInfo;
        type PostInfo = self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::PostDispatchInfo;
        fn dispatch(
            self,
            origin: RuntimeOrigin,
        ) -> self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::DispatchResultWithPostInfo {
            if !<Self::RuntimeOrigin as self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::OriginTrait>::filter_call(
                &origin,
                &self,
            ) {
                return self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_std::result::Result::Err(
                    frame_system::Error::<MockRuntime>::CallFiltered.into(),
                );
            }
            self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::UnfilteredDispatchable::dispatch_bypass_filter(
                self,
                origin,
            )
        }
    }
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::UnfilteredDispatchable
    for RuntimeCall {
        type RuntimeOrigin = RuntimeOrigin;
        fn dispatch_bypass_filter(
            self,
            origin: RuntimeOrigin,
        ) -> self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::DispatchResultWithPostInfo {
            match self {
                RuntimeCall::System(call) => {
                    self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::UnfilteredDispatchable::dispatch_bypass_filter(
                        call,
                        origin,
                    )
                }
                RuntimeCall::Balances(call) => {
                    self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::UnfilteredDispatchable::dispatch_bypass_filter(
                        call,
                        origin,
                    )
                }
                RuntimeCall::Interface(call) => {
                    self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::UnfilteredDispatchable::dispatch_bypass_filter(
                        call,
                        origin,
                    )
                }
            }
        }
    }
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::IsSubType<
        self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
            System,
            MockRuntime,
        >,
    > for RuntimeCall {
        #[allow(unreachable_patterns)]
        fn is_sub_type(
            &self,
        ) -> Option<
            &self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                System,
                MockRuntime,
            >,
        > {
            match self {
                RuntimeCall::System(call) => Some(call),
                _ => None,
            }
        }
    }
    impl From<
        self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
            System,
            MockRuntime,
        >,
    > for RuntimeCall {
        fn from(
            call: self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                System,
                MockRuntime,
            >,
        ) -> Self {
            RuntimeCall::System(call)
        }
    }
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::IsSubType<
        self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
            Balances,
            MockRuntime,
        >,
    > for RuntimeCall {
        #[allow(unreachable_patterns)]
        fn is_sub_type(
            &self,
        ) -> Option<
            &self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                Balances,
                MockRuntime,
            >,
        > {
            match self {
                RuntimeCall::Balances(call) => Some(call),
                _ => None,
            }
        }
    }
    impl From<
        self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
            Balances,
            MockRuntime,
        >,
    > for RuntimeCall {
        fn from(
            call: self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                Balances,
                MockRuntime,
            >,
        ) -> Self {
            RuntimeCall::Balances(call)
        }
    }
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::IsSubType<
        self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
            Interface,
            MockRuntime,
        >,
    > for RuntimeCall {
        #[allow(unreachable_patterns)]
        fn is_sub_type(
            &self,
        ) -> Option<
            &self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                Interface,
                MockRuntime,
            >,
        > {
            match self {
                RuntimeCall::Interface(call) => Some(call),
                _ => None,
            }
        }
    }
    impl From<
        self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
            Interface,
            MockRuntime,
        >,
    > for RuntimeCall {
        fn from(
            call: self::sp_api_hidden_includes_construct_runtime::hidden_include::dispatch::CallableCallFor<
                Interface,
                MockRuntime,
            >,
        ) -> Self {
            RuntimeCall::Interface(call)
        }
    }
    impl MockRuntime {
        pub fn metadata() -> self::sp_api_hidden_includes_construct_runtime::hidden_include::metadata::RuntimeMetadataPrefixed {
            self::sp_api_hidden_includes_construct_runtime::hidden_include::metadata::RuntimeMetadataLastVersion::new(
                    <[_]>::into_vec(
                        #[rustc_box]
                        ::alloc::boxed::Box::new([
                            self::sp_api_hidden_includes_construct_runtime::hidden_include::metadata::PalletMetadata {
                                name: "System",
                                index: 0u8,
                                storage: Some(
                                    frame_system::Pallet::<MockRuntime>::storage_metadata(),
                                ),
                                calls: Some(
                                    frame_system::Pallet::<MockRuntime>::call_functions(),
                                ),
                                event: Some(self::sp_api_hidden_includes_construct_runtime::hidden_include::metadata::PalletEventMetadata {
                                    ty: self::sp_api_hidden_includes_construct_runtime::hidden_include::scale_info::meta_type::<
                                        frame_system::Event<MockRuntime>,
                                    >(),
                                }),
                                constants: frame_system::Pallet::<
                                    MockRuntime,
                                >::pallet_constants_metadata(),
                                error: frame_system::Pallet::<MockRuntime>::error_metadata(),
                            },
                            self::sp_api_hidden_includes_construct_runtime::hidden_include::metadata::PalletMetadata {
                                name: "Balances",
                                index: 1u8,
                                storage: Some(
                                    pallet_balances::Pallet::<MockRuntime>::storage_metadata(),
                                ),
                                calls: Some(
                                    pallet_balances::Pallet::<MockRuntime>::call_functions(),
                                ),
                                event: Some(self::sp_api_hidden_includes_construct_runtime::hidden_include::metadata::PalletEventMetadata {
                                    ty: self::sp_api_hidden_includes_construct_runtime::hidden_include::scale_info::meta_type::<
                                        pallet_balances::Event<MockRuntime>,
                                    >(),
                                }),
                                constants: pallet_balances::Pallet::<
                                    MockRuntime,
                                >::pallet_constants_metadata(),
                                error: pallet_balances::Pallet::<
                                    MockRuntime,
                                >::error_metadata(),
                            },
                            self::sp_api_hidden_includes_construct_runtime::hidden_include::metadata::PalletMetadata {
                                name: "Interface",
                                index: 255u8,
                                storage: None,
                                calls: Some(
                                    pallet_interface::Pallet::<MockRuntime>::call_functions(),
                                ),
                                event: None,
                                constants: pallet_interface::Pallet::<
                                    MockRuntime,
                                >::pallet_constants_metadata(),
                                error: pallet_interface::Pallet::<
                                    MockRuntime,
                                >::error_metadata(),
                            },
                        ]),
                    ),
                    self::sp_api_hidden_includes_construct_runtime::hidden_include::metadata::ExtrinsicMetadata {
                        ty: self::sp_api_hidden_includes_construct_runtime::hidden_include::scale_info::meta_type::<
                            UncheckedExtrinsic,
                        >(),
                        version: <UncheckedExtrinsic as self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_runtime::traits::ExtrinsicMetadata>::VERSION,
                        signed_extensions: <<UncheckedExtrinsic as self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_runtime::traits::ExtrinsicMetadata>::SignedExtensions as self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_runtime::traits::SignedExtension>::metadata()
                            .into_iter()
                            .map(|meta| self::sp_api_hidden_includes_construct_runtime::hidden_include::metadata::SignedExtensionMetadata {
                                identifier: meta.identifier,
                                ty: meta.ty,
                                additional_signed: meta.additional_signed,
                            })
                            .collect(),
                    },
                    self::sp_api_hidden_includes_construct_runtime::hidden_include::scale_info::meta_type::<
                        MockRuntime,
                    >(),
                )
                .into()
        }
    }
    #[cfg(any(feature = "std", test))]
    pub type SystemConfig = frame_system::GenesisConfig;
    #[cfg(any(feature = "std", test))]
    pub type BalancesConfig = pallet_balances::GenesisConfig<MockRuntime>;
    #[cfg(any(feature = "std", test))]
    use self::sp_api_hidden_includes_construct_runtime::hidden_include::serde as __genesis_config_serde_import__;
    #[cfg(any(feature = "std", test))]
    #[serde(rename_all = "camelCase")]
    #[serde(deny_unknown_fields)]
    #[serde(crate = "__genesis_config_serde_import__")]
    pub struct GenesisConfig {
        pub system: SystemConfig,
        pub balances: BalancesConfig,
    }
    #[doc(hidden)]
    #[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
    const _: () = {
        use __genesis_config_serde_import__ as _serde;
        #[automatically_derived]
        impl __genesis_config_serde_import__::Serialize for GenesisConfig {
            fn serialize<__S>(
                &self,
                __serializer: __S,
            ) -> __genesis_config_serde_import__::__private::Result<__S::Ok, __S::Error>
            where
                __S: __genesis_config_serde_import__::Serializer,
            {
                let mut __serde_state = match _serde::Serializer::serialize_struct(
                    __serializer,
                    "GenesisConfig",
                    false as usize + 1 + 1,
                ) {
                    _serde::__private::Ok(__val) => __val,
                    _serde::__private::Err(__err) => {
                        return _serde::__private::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(
                    &mut __serde_state,
                    "system",
                    &self.system,
                ) {
                    _serde::__private::Ok(__val) => __val,
                    _serde::__private::Err(__err) => {
                        return _serde::__private::Err(__err);
                    }
                };
                match _serde::ser::SerializeStruct::serialize_field(
                    &mut __serde_state,
                    "balances",
                    &self.balances,
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
        use __genesis_config_serde_import__ as _serde;
        #[automatically_derived]
        impl<'de> __genesis_config_serde_import__::Deserialize<'de> for GenesisConfig {
            fn deserialize<__D>(
                __deserializer: __D,
            ) -> __genesis_config_serde_import__::__private::Result<Self, __D::Error>
            where
                __D: __genesis_config_serde_import__::Deserializer<'de>,
            {
                #[allow(non_camel_case_types)]
                #[doc(hidden)]
                enum __Field {
                    __field0,
                    __field1,
                }
                #[doc(hidden)]
                struct __FieldVisitor;
                impl<'de> _serde::de::Visitor<'de> for __FieldVisitor {
                    type Value = __Field;
                    fn expecting(
                        &self,
                        __formatter: &mut _serde::__private::Formatter,
                    ) -> _serde::__private::fmt::Result {
                        _serde::__private::Formatter::write_str(
                            __formatter,
                            "field identifier",
                        )
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
                            _ => {
                                _serde::__private::Err(
                                    _serde::de::Error::invalid_value(
                                        _serde::de::Unexpected::Unsigned(__value),
                                        &"field index 0 <= i < 2",
                                    ),
                                )
                            }
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
                            "system" => _serde::__private::Ok(__Field::__field0),
                            "balances" => _serde::__private::Ok(__Field::__field1),
                            _ => {
                                _serde::__private::Err(
                                    _serde::de::Error::unknown_field(__value, FIELDS),
                                )
                            }
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
                            b"system" => _serde::__private::Ok(__Field::__field0),
                            b"balances" => _serde::__private::Ok(__Field::__field1),
                            _ => {
                                let __value = &_serde::__private::from_utf8_lossy(__value);
                                _serde::__private::Err(
                                    _serde::de::Error::unknown_field(__value, FIELDS),
                                )
                            }
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
                        _serde::Deserializer::deserialize_identifier(
                            __deserializer,
                            __FieldVisitor,
                        )
                    }
                }
                #[doc(hidden)]
                struct __Visitor<'de> {
                    marker: _serde::__private::PhantomData<GenesisConfig>,
                    lifetime: _serde::__private::PhantomData<&'de ()>,
                }
                impl<'de> _serde::de::Visitor<'de> for __Visitor<'de> {
                    type Value = GenesisConfig;
                    fn expecting(
                        &self,
                        __formatter: &mut _serde::__private::Formatter,
                    ) -> _serde::__private::fmt::Result {
                        _serde::__private::Formatter::write_str(
                            __formatter,
                            "struct GenesisConfig",
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
                        let __field0 = match match _serde::de::SeqAccess::next_element::<
                            SystemConfig,
                        >(&mut __seq) {
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
                                        &"struct GenesisConfig with 2 elements",
                                    ),
                                );
                            }
                        };
                        let __field1 = match match _serde::de::SeqAccess::next_element::<
                            BalancesConfig,
                        >(&mut __seq) {
                            _serde::__private::Ok(__val) => __val,
                            _serde::__private::Err(__err) => {
                                return _serde::__private::Err(__err);
                            }
                        } {
                            _serde::__private::Some(__value) => __value,
                            _serde::__private::None => {
                                return _serde::__private::Err(
                                    _serde::de::Error::invalid_length(
                                        1usize,
                                        &"struct GenesisConfig with 2 elements",
                                    ),
                                );
                            }
                        };
                        _serde::__private::Ok(GenesisConfig {
                            system: __field0,
                            balances: __field1,
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
                        let mut __field0: _serde::__private::Option<SystemConfig> = _serde::__private::None;
                        let mut __field1: _serde::__private::Option<BalancesConfig> = _serde::__private::None;
                        while let _serde::__private::Some(__key)
                            = match _serde::de::MapAccess::next_key::<
                                __Field,
                            >(&mut __map) {
                                _serde::__private::Ok(__val) => __val,
                                _serde::__private::Err(__err) => {
                                    return _serde::__private::Err(__err);
                                }
                            } {
                            match __key {
                                __Field::__field0 => {
                                    if _serde::__private::Option::is_some(&__field0) {
                                        return _serde::__private::Err(
                                            <__A::Error as _serde::de::Error>::duplicate_field("system"),
                                        );
                                    }
                                    __field0 = _serde::__private::Some(
                                        match _serde::de::MapAccess::next_value::<
                                            SystemConfig,
                                        >(&mut __map) {
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
                                                "balances",
                                            ),
                                        );
                                    }
                                    __field1 = _serde::__private::Some(
                                        match _serde::de::MapAccess::next_value::<
                                            BalancesConfig,
                                        >(&mut __map) {
                                            _serde::__private::Ok(__val) => __val,
                                            _serde::__private::Err(__err) => {
                                                return _serde::__private::Err(__err);
                                            }
                                        },
                                    );
                                }
                            }
                        }
                        let __field0 = match __field0 {
                            _serde::__private::Some(__field0) => __field0,
                            _serde::__private::None => {
                                match _serde::__private::de::missing_field("system") {
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
                                match _serde::__private::de::missing_field("balances") {
                                    _serde::__private::Ok(__val) => __val,
                                    _serde::__private::Err(__err) => {
                                        return _serde::__private::Err(__err);
                                    }
                                }
                            }
                        };
                        _serde::__private::Ok(GenesisConfig {
                            system: __field0,
                            balances: __field1,
                        })
                    }
                }
                #[doc(hidden)]
                const FIELDS: &'static [&'static str] = &["system", "balances"];
                _serde::Deserializer::deserialize_struct(
                    __deserializer,
                    "GenesisConfig",
                    FIELDS,
                    __Visitor {
                        marker: _serde::__private::PhantomData::<GenesisConfig>,
                        lifetime: _serde::__private::PhantomData,
                    },
                )
            }
        }
    };
    #[automatically_derived]
    impl ::core::default::Default for GenesisConfig {
        #[inline]
        fn default() -> GenesisConfig {
            GenesisConfig {
                system: ::core::default::Default::default(),
                balances: ::core::default::Default::default(),
            }
        }
    }
    #[cfg(any(feature = "std", test))]
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_runtime::BuildStorage
    for GenesisConfig {
        fn assimilate_storage(
            &self,
            storage: &mut self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_runtime::Storage,
        ) -> std::result::Result<(), String> {
            self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_runtime::BuildModuleGenesisStorage::<
                MockRuntime,
                frame_system::__InherentHiddenInstance,
            >::build_module_genesis_storage(&self.system, storage)?;
            self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_runtime::BuildModuleGenesisStorage::<
                MockRuntime,
                pallet_balances::__InherentHiddenInstance,
            >::build_module_genesis_storage(&self.balances, storage)?;
            self::sp_api_hidden_includes_construct_runtime::hidden_include::BasicExternalities::execute_with_storage(
                storage,
                || {
                    <AllPalletsWithSystem as self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::OnGenesis>::on_genesis();
                },
            );
            Ok(())
        }
    }
    trait InherentDataExt {
        fn create_extrinsics(
            &self,
        ) -> self::sp_api_hidden_includes_construct_runtime::hidden_include::inherent::Vec<
            <Block as self::sp_api_hidden_includes_construct_runtime::hidden_include::inherent::BlockT>::Extrinsic,
        >;
        fn check_extrinsics(
            &self,
            block: &Block,
        ) -> self::sp_api_hidden_includes_construct_runtime::hidden_include::inherent::CheckInherentsResult;
    }
    impl InherentDataExt
    for self::sp_api_hidden_includes_construct_runtime::hidden_include::inherent::InherentData {
        fn create_extrinsics(
            &self,
        ) -> self::sp_api_hidden_includes_construct_runtime::hidden_include::inherent::Vec<
            <Block as self::sp_api_hidden_includes_construct_runtime::hidden_include::inherent::BlockT>::Extrinsic,
        > {
            use self::sp_api_hidden_includes_construct_runtime::hidden_include::inherent::ProvideInherent;
            let mut inherents = Vec::new();
            inherents
        }
        fn check_extrinsics(
            &self,
            block: &Block,
        ) -> self::sp_api_hidden_includes_construct_runtime::hidden_include::inherent::CheckInherentsResult {
            use self::sp_api_hidden_includes_construct_runtime::hidden_include::inherent::{
                ProvideInherent, IsFatalError,
            };
            use self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::{
                IsSubType, ExtrinsicCall,
            };
            use self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_runtime::traits::Block as _;
            let mut result = self::sp_api_hidden_includes_construct_runtime::hidden_include::inherent::CheckInherentsResult::new();
            for xt in block.extrinsics() {
                if self::sp_api_hidden_includes_construct_runtime::hidden_include::inherent::Extrinsic::is_signed(
                        xt,
                    )
                    .unwrap_or(false)
                {
                    break;
                }
                let mut is_inherent = false;
                if !is_inherent {
                    break;
                }
            }
            result
        }
    }
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::EnsureInherentsAreFirst<
        Block,
    > for MockRuntime {
        fn ensure_inherents_are_first(block: &Block) -> Result<(), u32> {
            use self::sp_api_hidden_includes_construct_runtime::hidden_include::inherent::ProvideInherent;
            use self::sp_api_hidden_includes_construct_runtime::hidden_include::traits::{
                IsSubType, ExtrinsicCall,
            };
            use self::sp_api_hidden_includes_construct_runtime::hidden_include::sp_runtime::traits::Block as _;
            let mut first_signed_observed = false;
            for (i, xt) in block.extrinsics().iter().enumerate() {
                let is_signed = self::sp_api_hidden_includes_construct_runtime::hidden_include::inherent::Extrinsic::is_signed(
                        xt,
                    )
                    .unwrap_or(false);
                let is_inherent = if is_signed {
                    false
                } else {
                    let mut is_inherent = false;
                    is_inherent
                };
                if !is_inherent {
                    first_signed_observed = true;
                }
                if first_signed_observed && is_inherent {
                    return Err(i as u32);
                }
            }
            Ok(())
        }
    }
    impl self::sp_api_hidden_includes_construct_runtime::hidden_include::unsigned::ValidateUnsigned
    for MockRuntime {
        type Call = RuntimeCall;
        fn pre_dispatch(
            call: &Self::Call,
        ) -> Result<
            (),
            self::sp_api_hidden_includes_construct_runtime::hidden_include::unsigned::TransactionValidityError,
        > {
            #[allow(unreachable_patterns)]
            match call {
                _ => Ok(()),
            }
        }
        fn validate_unsigned(
            #[allow(unused_variables)]
            source: self::sp_api_hidden_includes_construct_runtime::hidden_include::unsigned::TransactionSource,
            call: &Self::Call,
        ) -> self::sp_api_hidden_includes_construct_runtime::hidden_include::unsigned::TransactionValidity {
            #[allow(unreachable_patterns)]
            match call {
                _ => {
                    self::sp_api_hidden_includes_construct_runtime::hidden_include::unsigned::UnknownTransaction::NoUnsignedValidator
                        .into()
                }
            }
        }
    }
    const _: () = if !(<frame_system::Error<
        MockRuntime,
    > as ::frame_support::traits::PalletError>::MAX_ENCODED_SIZE
        <= ::frame_support::MAX_MODULE_ERROR_ENCODED_SIZE)
    {
        {
            ::core::panicking::panic_fmt(
                format_args!(
                    "The maximum encoded size of the error type in the `System` pallet exceeds `MAX_MODULE_ERROR_ENCODED_SIZE`"
                ),
            );
        }
    };
    const _: () = if !(<pallet_balances::Error<
        MockRuntime,
    > as ::frame_support::traits::PalletError>::MAX_ENCODED_SIZE
        <= ::frame_support::MAX_MODULE_ERROR_ENCODED_SIZE)
    {
        {
            ::core::panicking::panic_fmt(
                format_args!(
                    "The maximum encoded size of the error type in the `Balances` pallet exceeds `MAX_MODULE_ERROR_ENCODED_SIZE`"
                ),
            );
        }
    };
    const _: () = if !(<pallet_interface::Error<
        MockRuntime,
    > as ::frame_support::traits::PalletError>::MAX_ENCODED_SIZE
        <= ::frame_support::MAX_MODULE_ERROR_ENCODED_SIZE)
    {
        {
            ::core::panicking::panic_fmt(
                format_args!(
                    "The maximum encoded size of the error type in the `Interface` pallet exceeds `MAX_MODULE_ERROR_ENCODED_SIZE`"
                ),
            );
        }
    };
    impl frame_system::Config for MockRuntime {
        type BaseCallFilter = frame_support::traits::Everything;
        type BlockWeights = ();
        type BlockLength = ();
        type RuntimeOrigin = RuntimeOrigin;
        type Index = u64;
        type BlockNumber = u64;
        type Hash = H256;
        type RuntimeCall = RuntimeCall;
        type Hashing = BlakeTwo256;
        type AccountId = AccountId;
        type Lookup = IdentityLookup<Self::AccountId>;
        type Header = Header;
        type RuntimeEvent = RuntimeEvent;
        type BlockHashCount = ConstU64<250>;
        type DbWeight = ();
        type Version = ();
        type PalletInfo = PalletInfo;
        type AccountData = pallet_balances::AccountData<Balance>;
        type OnNewAccount = ();
        type OnKilledAccount = ();
        type SystemWeightInfo = ();
        type SS58Prefix = ();
        type OnSetCode = ();
        type MaxConsumers = ConstU32<16>;
    }
    impl pallet_interface::Config for MockRuntime {
        type RuntimeEvent = RuntimeEvent;
        type Interface = InterfaceCall;
    }
    struct AccountSelector;
    impl Selector for AccountSelector {
        type Selectable = interfaces::pip20::AccountIdSelectable;
        type Selected = AccountId;
        fn select(selectable: Self::Selectable) -> SelectorResult<Self::Selected> {
            ::core::panicking::panic("not yet implemented")
        }
    }
    struct CurrencySelector;
    impl Selector for CurrencySelector {
        type Selectable = interfaces::pip20::CurrencyIdSelectable;
        type Selected = CurrencyId;
        fn select(selectable: Self::Selectable) -> SelectorResult<Self::Selected> {
            ::core::panicking::panic("not yet implemented")
        }
    }
    struct BalanceSelector;
    impl Selector for BalanceSelector {
        type Selectable = interfaces::pip20::BalanceSelectable;
        type Selected = Balance;
        fn select(selectable: Self::Selectable) -> SelectorResult<Self::Selected> {
            ::core::panicking::panic("not yet implemented")
        }
    }
    impl interfaces::pip20::Pip20 for MockRuntime {
        /// A means for converting between from a [u8; 32] to the native chains account id.
        type SelectAccount = AccountSelector;
        /// The chains native currency type.
        type Currency = CurrencyId;
        /// A means for converting between from a `H256` to the chains native currency.
        type SelectCurrency = CurrencySelector;
        /// The chains native balance type.
        type Balance = Balance;
        /// A means for converting between from a u128 to the chains native balance.
        type SelectBalance = BalanceSelector;
        fn free_balance(
            currency: Select<Self::SelectCurrency>,
            who: Select<Self::SelectAccount>,
        ) -> ViewResult<BalanceSelector> {
            ::core::panicking::panic("not yet implemented")
        }
        fn balances(
            who: Select<Self::SelectAccount>,
        ) -> ViewResult<Vec<(CurrencySelector, BalanceSelector)>> {
            ::core::panicking::panic("not yet implemented")
        }
        fn transfer(
            origin: Self::RuntimeOrigin,
            currency: Select<SelectCurrency>,
            recv: Select<Self::SelectAccount>,
            amount: Select<Self::SelectBalance>,
        ) -> CallResult {
            ::core::panicking::panic("not yet implemented")
        }
        fn burn(
            origin: Self::RuntimeOrigin,
            currency: Select<Self::SelectCurrency>,
            from: Select<Self::SelectAccount>,
            amount: Select<Self::SelectBalance>,
        ) -> CallResult {
            ::core::panicking::panic("not yet implemented")
        }
        fn approve(
            origin: Self::RuntimeOrigin,
            currency: Select<Self::SelectCurrency>,
            recv: Select<Self::SelectAccount>,
            amount: Select<Self::SelectBalance>,
        ) -> CallResult {
            ::core::panicking::panic("not yet implemented")
        }
    }
    impl interfaces::pip42::Pip42 for MockRuntime {
        type MaxRemark = ConstU32<64>;
        fn remark(bytes: BoundedVec<u8, Self::MaxRemark>) -> CallResult {
            ::core::panicking::panic("not yet implemented")
        }
    }
    pub enum InterfaceCall {
        #[codec(index = 20u8)]
        Pip20(interfaces::pip20::Call<MockRuntime>),
        #[codec(index = 42u8)]
        Pip42(interfaces::pip42::Call<MockRuntime>),
    }
    #[allow(deprecated)]
    const _: () = {
        #[automatically_derived]
        impl ::codec::Decode for InterfaceCall {
            fn decode<__CodecInputEdqy: ::codec::Input>(
                __codec_input_edqy: &mut __CodecInputEdqy,
            ) -> ::core::result::Result<Self, ::codec::Error> {
                match __codec_input_edqy
                    .read_byte()
                    .map_err(|e| {
                        e
                            .chain(
                                "Could not decode `InterfaceCall`, failed to read variant byte",
                            )
                    })?
                {
                    __codec_x_edqy if __codec_x_edqy == 20u8 as ::core::primitive::u8 => {
                        ::core::result::Result::Ok(
                            InterfaceCall::Pip20({
                                let __codec_res_edqy = <interfaces::pip20::Call<
                                    MockRuntime,
                                > as ::codec::Decode>::decode(__codec_input_edqy);
                                match __codec_res_edqy {
                                    ::core::result::Result::Err(e) => {
                                        return ::core::result::Result::Err(
                                            e.chain("Could not decode `InterfaceCall::Pip20.0`"),
                                        );
                                    }
                                    ::core::result::Result::Ok(__codec_res_edqy) => {
                                        __codec_res_edqy
                                    }
                                }
                            }),
                        )
                    }
                    __codec_x_edqy if __codec_x_edqy == 42u8 as ::core::primitive::u8 => {
                        ::core::result::Result::Ok(
                            InterfaceCall::Pip42({
                                let __codec_res_edqy = <interfaces::pip42::Call<
                                    MockRuntime,
                                > as ::codec::Decode>::decode(__codec_input_edqy);
                                match __codec_res_edqy {
                                    ::core::result::Result::Err(e) => {
                                        return ::core::result::Result::Err(
                                            e.chain("Could not decode `InterfaceCall::Pip42.0`"),
                                        );
                                    }
                                    ::core::result::Result::Ok(__codec_res_edqy) => {
                                        __codec_res_edqy
                                    }
                                }
                            }),
                        )
                    }
                    _ => {
                        ::core::result::Result::Err(
                            <_ as ::core::convert::Into<
                                _,
                            >>::into(
                                "Could not decode `InterfaceCall`, variant doesn't exist",
                            ),
                        )
                    }
                }
            }
        }
    };
    #[allow(deprecated)]
    const _: () = {
        #[automatically_derived]
        impl ::codec::Encode for InterfaceCall {
            fn encode_to<__CodecOutputEdqy: ::codec::Output + ?::core::marker::Sized>(
                &self,
                __codec_dest_edqy: &mut __CodecOutputEdqy,
            ) {
                match *self {
                    InterfaceCall::Pip20(ref aa) => {
                        __codec_dest_edqy.push_byte(20u8 as ::core::primitive::u8);
                        ::codec::Encode::encode_to(aa, __codec_dest_edqy);
                    }
                    InterfaceCall::Pip42(ref aa) => {
                        __codec_dest_edqy.push_byte(42u8 as ::core::primitive::u8);
                        ::codec::Encode::encode_to(aa, __codec_dest_edqy);
                    }
                    _ => {}
                }
            }
        }
        #[automatically_derived]
        impl ::codec::EncodeLike for InterfaceCall {}
    };
    #[automatically_derived]
    impl ::core::clone::Clone for InterfaceCall {
        #[inline]
        fn clone(&self) -> InterfaceCall {
            match self {
                InterfaceCall::Pip20(__self_0) => {
                    InterfaceCall::Pip20(::core::clone::Clone::clone(__self_0))
                }
                InterfaceCall::Pip42(__self_0) => {
                    InterfaceCall::Pip42(::core::clone::Clone::clone(__self_0))
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for InterfaceCall {}
    #[automatically_derived]
    impl ::core::cmp::PartialEq for InterfaceCall {
        #[inline]
        fn eq(&self, other: &InterfaceCall) -> bool {
            let __self_tag = ::core::intrinsics::discriminant_value(self);
            let __arg1_tag = ::core::intrinsics::discriminant_value(other);
            __self_tag == __arg1_tag
                && match (self, other) {
                    (InterfaceCall::Pip20(__self_0), InterfaceCall::Pip20(__arg1_0)) => {
                        *__self_0 == *__arg1_0
                    }
                    (InterfaceCall::Pip42(__self_0), InterfaceCall::Pip42(__arg1_0)) => {
                        *__self_0 == *__arg1_0
                    }
                    _ => unsafe { ::core::intrinsics::unreachable() }
                }
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralEq for InterfaceCall {}
    #[automatically_derived]
    impl ::core::cmp::Eq for InterfaceCall {
        #[inline]
        #[doc(hidden)]
        #[no_coverage]
        fn assert_receiver_is_total_eq(&self) -> () {
            let _: ::core::cmp::AssertParamIsEq<interfaces::pip20::Call<MockRuntime>>;
            let _: ::core::cmp::AssertParamIsEq<interfaces::pip42::Call<MockRuntime>>;
        }
    }
    impl frame_support::dispatch::GetDispatchInfo for InterfaceCall {
        fn get_dispatch_info(&self) -> frame_support::dispatch::DispatchInfo {
            ::core::panicking::panic("not yet implemented")
        }
    }
    impl frame_support::traits::UnfilteredDispatchable for InterfaceCall {
        type RuntimeOrigin = <MockRuntime as frame_system::Config>::RuntimeOrigin;
        fn dispatch_bypass_filter(
            self,
            origin: Self::RuntimeOrigin,
        ) -> frame_support::dispatch::DispatchResultWithPostInfo {
            frame_support::dispatch_context::run_in_context(|| {
                match self {
                    Self::Pip20(interface) => {
                        let __within_span__ = {
                            use ::tracing::__macro_support::Callsite as _;
                            static CALLSITE: ::tracing::callsite::DefaultCallsite = {
                                static META: ::tracing::Metadata<'static> = {
                                    ::tracing_core::metadata::Metadata::new(
                                        "Pip20",
                                        "pallet_interface::mock",
                                        ::tracing::Level::TRACE,
                                        Some("frame/interface/src/mock.rs"),
                                        Some(290u32),
                                        Some("pallet_interface::mock"),
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
                                ::tracing::Span::new(
                                    meta,
                                    &{ meta.fields().value_set(&[]) },
                                )
                            } else {
                                let span = ::tracing::__macro_support::__disabled_span(
                                    CALLSITE.metadata(),
                                );
                                {};
                                span
                            }
                        };
                        let __tracing_guard__ = __within_span__.enter();
                        frame_support::traits::UnfilteredDispatchable::dispatch_bypass_filter(
                                interface,
                                origin,
                            )
                            .map(Into::into)
                            .map_err(Into::into)
                    }
                    Self::Pip42(interface) => {
                        let __within_span__ = {
                            use ::tracing::__macro_support::Callsite as _;
                            static CALLSITE: ::tracing::callsite::DefaultCallsite = {
                                static META: ::tracing::Metadata<'static> = {
                                    ::tracing_core::metadata::Metadata::new(
                                        "Pip42",
                                        "pallet_interface::mock",
                                        ::tracing::Level::TRACE,
                                        Some("frame/interface/src/mock.rs"),
                                        Some(290u32),
                                        Some("pallet_interface::mock"),
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
                                ::tracing::Span::new(
                                    meta,
                                    &{ meta.fields().value_set(&[]) },
                                )
                            } else {
                                let span = ::tracing::__macro_support::__disabled_span(
                                    CALLSITE.metadata(),
                                );
                                {};
                                span
                            }
                        };
                        let __tracing_guard__ = __within_span__.enter();
                        frame_support::traits::UnfilteredDispatchable::dispatch_bypass_filter(
                                interface,
                                origin,
                            )
                            .map(Into::into)
                            .map_err(Into::into)
                    }
                }
            })
        }
    }
    impl frame_support::traits::GetCallMetadata for InterfaceCall {
        fn get_module_names() -> &'static [&'static str] {
            ::core::panicking::panic("not yet implemented")
        }
        fn get_call_names(module: &str) -> &'static [&'static str] {
            ::core::panicking::panic("not yet implemented")
        }
        fn get_call_metadata(&self) -> frame_support::traits::CallMetadata {
            ::core::panicking::panic("not yet implemented")
        }
    }
    const _: () = {};
    pub enum InterfaceView {
        #[codec(index = 20u8)]
        Pip20(interfaces::pip20::View<MockRuntime>),
    }
    #[allow(deprecated)]
    const _: () = {
        #[automatically_derived]
        impl ::codec::Decode for InterfaceView {
            fn decode<__CodecInputEdqy: ::codec::Input>(
                __codec_input_edqy: &mut __CodecInputEdqy,
            ) -> ::core::result::Result<Self, ::codec::Error> {
                match __codec_input_edqy
                    .read_byte()
                    .map_err(|e| {
                        e
                            .chain(
                                "Could not decode `InterfaceView`, failed to read variant byte",
                            )
                    })?
                {
                    __codec_x_edqy if __codec_x_edqy == 20u8 as ::core::primitive::u8 => {
                        ::core::result::Result::Ok(
                            InterfaceView::Pip20({
                                let __codec_res_edqy = <interfaces::pip20::View<
                                    MockRuntime,
                                > as ::codec::Decode>::decode(__codec_input_edqy);
                                match __codec_res_edqy {
                                    ::core::result::Result::Err(e) => {
                                        return ::core::result::Result::Err(
                                            e.chain("Could not decode `InterfaceView::Pip20.0`"),
                                        );
                                    }
                                    ::core::result::Result::Ok(__codec_res_edqy) => {
                                        __codec_res_edqy
                                    }
                                }
                            }),
                        )
                    }
                    _ => {
                        ::core::result::Result::Err(
                            <_ as ::core::convert::Into<
                                _,
                            >>::into(
                                "Could not decode `InterfaceView`, variant doesn't exist",
                            ),
                        )
                    }
                }
            }
        }
    };
    #[allow(deprecated)]
    const _: () = {
        #[automatically_derived]
        impl ::codec::Encode for InterfaceView {
            fn encode_to<__CodecOutputEdqy: ::codec::Output + ?::core::marker::Sized>(
                &self,
                __codec_dest_edqy: &mut __CodecOutputEdqy,
            ) {
                match *self {
                    InterfaceView::Pip20(ref aa) => {
                        __codec_dest_edqy.push_byte(20u8 as ::core::primitive::u8);
                        ::codec::Encode::encode_to(aa, __codec_dest_edqy);
                    }
                    _ => {}
                }
            }
        }
        #[automatically_derived]
        impl ::codec::EncodeLike for InterfaceView {}
    };
    #[automatically_derived]
    impl ::core::clone::Clone for InterfaceView {
        #[inline]
        fn clone(&self) -> InterfaceView {
            match self {
                InterfaceView::Pip20(__self_0) => {
                    InterfaceView::Pip20(::core::clone::Clone::clone(__self_0))
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralPartialEq for InterfaceView {}
    #[automatically_derived]
    impl ::core::cmp::PartialEq for InterfaceView {
        #[inline]
        fn eq(&self, other: &InterfaceView) -> bool {
            match (self, other) {
                (InterfaceView::Pip20(__self_0), InterfaceView::Pip20(__arg1_0)) => {
                    *__self_0 == *__arg1_0
                }
            }
        }
    }
    #[automatically_derived]
    impl ::core::marker::StructuralEq for InterfaceView {}
    #[automatically_derived]
    impl ::core::cmp::Eq for InterfaceView {
        #[inline]
        #[doc(hidden)]
        #[no_coverage]
        fn assert_receiver_is_total_eq(&self) -> () {
            let _: ::core::cmp::AssertParamIsEq<interfaces::pip20::View<MockRuntime>>;
        }
    }
    impl frame_support::interface::View for InterfaceView {
        fn view(self) -> frame_support::interface::ViewResult<Vec<u8>> {
            ::core::panicking::panic("not yet implemented")
        }
    }
    const _: () = {};
    /// Executive: handles dispatch to the various modules.
    pub type Executive = frame_executive::Executive<
        Runtime,
        Block,
        frame_system::ChainContext<Runtime>,
        Runtime,
        AllPalletsWithSystem,
        (),
    >;
    #[doc(hidden)]
    mod sp_api_hidden_includes_IMPL_RUNTIME_APIS {
        pub extern crate sp_api as sp_api;
    }
    pub struct RuntimeApi {}
    /// Implements all runtime apis for the client side.
    #[cfg(any(feature = "std", test))]
    pub struct RuntimeApiImpl<
        Block: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::BlockT,
        C: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt<Block>
            + 'static,
    > {
        call: &'static C,
        commit_on_success: std::cell::RefCell<bool>,
        changes: std::cell::RefCell<
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::OverlayedChanges,
        >,
        storage_transaction_cache: std::cell::RefCell<
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::StorageTransactionCache<
                Block,
                C::StateBackend,
            >,
        >,
        recorder: std::option::Option<
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ProofRecorder<Block>,
        >,
    }
    #[cfg(any(feature = "std", test))]
    impl<
        Block: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::BlockT,
        C: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt<Block>,
    > self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ApiExt<Block>
    for RuntimeApiImpl<Block, C> {
        type StateBackend = C::StateBackend;
        fn execute_in_transaction<
            F: FnOnce(
                    &Self,
                ) -> self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::TransactionOutcome<
                        R,
                    >,
            R,
        >(&self, call: F) -> R
        where
            Self: Sized,
        {
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::OverlayedChanges::start_transaction(
                &mut std::cell::RefCell::borrow_mut(&self.changes),
            );
            *std::cell::RefCell::borrow_mut(&self.commit_on_success) = false;
            let res = call(self);
            *std::cell::RefCell::borrow_mut(&self.commit_on_success) = true;
            self.commit_or_rollback(
                match res {
                    self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::TransactionOutcome::Commit(
                        _,
                    ) => true,
                    _ => false,
                },
            );
            res.into_inner()
        }
        fn has_api<
            A: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::RuntimeApiInfo
                + ?Sized,
        >(
            &self,
            at: <Block as self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::BlockT>::Hash,
        ) -> std::result::Result<
            bool,
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ApiError,
        >
        where
            Self: Sized,
        {
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt::<
                Block,
            >::runtime_version_at(self.call, at)
                .map(|v| self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::RuntimeVersion::has_api_with(
                    &v,
                    &A::ID,
                    |v| v == A::VERSION,
                ))
        }
        fn has_api_with<
            A: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::RuntimeApiInfo
                + ?Sized,
            P: Fn(u32) -> bool,
        >(
            &self,
            at: <Block as self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::BlockT>::Hash,
            pred: P,
        ) -> std::result::Result<
            bool,
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ApiError,
        >
        where
            Self: Sized,
        {
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt::<
                Block,
            >::runtime_version_at(self.call, at)
                .map(|v| self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::RuntimeVersion::has_api_with(
                    &v,
                    &A::ID,
                    pred,
                ))
        }
        fn api_version<
            A: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::RuntimeApiInfo
                + ?Sized,
        >(
            &self,
            at: <Block as self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::BlockT>::Hash,
        ) -> std::result::Result<
            Option<u32>,
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ApiError,
        >
        where
            Self: Sized,
        {
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt::<
                Block,
            >::runtime_version_at(self.call, at)
                .map(|v| self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::RuntimeVersion::api_version(
                    &v,
                    &A::ID,
                ))
        }
        fn record_proof(&mut self) {
            self.recorder = std::option::Option::Some(std::default::Default::default());
        }
        fn proof_recorder(
            &self,
        ) -> std::option::Option<
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ProofRecorder<Block>,
        > {
            std::clone::Clone::clone(&self.recorder)
        }
        fn extract_proof(
            &mut self,
        ) -> std::option::Option<
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::StorageProof,
        > {
            let recorder = std::option::Option::take(&mut self.recorder);
            std::option::Option::map(
                recorder,
                |recorder| {
                    self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ProofRecorder::<
                        Block,
                    >::drain_storage_proof(recorder)
                },
            )
        }
        fn into_storage_changes(
            &self,
            backend: &Self::StateBackend,
            parent_hash: Block::Hash,
        ) -> core::result::Result<
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::StorageChanges<
                C::StateBackend,
                Block,
            >,
            String,
        >
        where
            Self: Sized,
        {
            let state_version = self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt::<
                Block,
            >::runtime_version_at(self.call, std::clone::Clone::clone(&parent_hash))
                .map(|v| self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::RuntimeVersion::state_version(
                    &v,
                ))
                .map_err(|e| {
                    let res = ::alloc::fmt::format(
                        format_args!("Failed to get state version: {0}", e),
                    );
                    res
                })?;
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::OverlayedChanges::into_storage_changes(
                std::cell::RefCell::take(&self.changes),
                backend,
                core::cell::RefCell::take(&self.storage_transaction_cache),
                state_version,
            )
        }
    }
    #[cfg(any(feature = "std", test))]
    impl<
        Block: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::BlockT,
        C,
    > self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ConstructRuntimeApi<
        Block,
        C,
    > for RuntimeApi
    where
        C: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt<Block>
            + 'static,
    {
        type RuntimeApi = RuntimeApiImpl<Block, C>;
        fn construct_runtime_api<'a>(
            call: &'a C,
        ) -> self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ApiRef<
            'a,
            Self::RuntimeApi,
        > {
            RuntimeApiImpl {
                call: unsafe { std::mem::transmute(call) },
                commit_on_success: true.into(),
                changes: std::default::Default::default(),
                recorder: std::default::Default::default(),
                storage_transaction_cache: std::default::Default::default(),
            }
                .into()
        }
    }
    #[cfg(any(feature = "std", test))]
    impl<
        Block: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::BlockT,
        C: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt<Block>,
    > RuntimeApiImpl<Block, C> {
        fn commit_or_rollback(&self, commit: bool) {
            let proof = "\
					We only close a transaction when we opened one ourself.
					Other parts of the runtime that make use of transactions (state-machine)
					also balance their transactions. The runtime cannot close client initiated
					transactions; qed";
            if *std::cell::RefCell::borrow(&self.commit_on_success) {
                let res = if commit {
                    self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::OverlayedChanges::commit_transaction(
                        &mut std::cell::RefCell::borrow_mut(&self.changes),
                    )
                } else {
                    self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::OverlayedChanges::rollback_transaction(
                        &mut std::cell::RefCell::borrow_mut(&self.changes),
                    )
                };
                std::result::Result::expect(res, proof);
            }
        }
    }
    impl sp_api::runtime_decl_for_Core::Core<Block> for MockRuntime {
        fn version() -> RuntimeVersion {
            VERSION
        }
        fn execute_block(block: Block) {
            Executive::execute_block(block)
        }
        fn initialize_block(header: &<Block as sp_runtime::traits::Block>::Header) {
            Executive::initialize_block(header)
        }
    }
    impl sp_api::runtime_decl_for_Metadata::Metadata<Block> for MockRuntime {
        fn metadata() -> OpaqueMetadata {
            sp_core::OpaqueMetadata::new(MockRuntime::metadata().into())
        }
    }
    impl frame_support::interface::runtime_decl_for_Interface::Interface<
        Block,
        InterfaceView,
    > for MockRuntime {
        fn view(view: InterfaceView) -> ViewResult<Vec<u8>> {
            view.view()
        }
    }
    #[cfg(any(feature = "std", test))]
    impl<
        __SR_API_BLOCK__: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::BlockT
            + std::panic::UnwindSafe + std::panic::RefUnwindSafe,
        RuntimeApiImplCall: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt<
                __SR_API_BLOCK__,
            > + 'static,
    > sp_api::Core<__SR_API_BLOCK__>
    for RuntimeApiImpl<__SR_API_BLOCK__, RuntimeApiImplCall>
    where
        RuntimeApiImplCall::StateBackend: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::StateBackend<
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::HashFor<
                __SR_API_BLOCK__,
            >,
        >,
        &'static RuntimeApiImplCall: Send,
        RuntimeVersion: std::panic::UnwindSafe + std::panic::RefUnwindSafe,
        __SR_API_BLOCK__: std::panic::UnwindSafe + std::panic::RefUnwindSafe,
        <__SR_API_BLOCK__ as sp_runtime::traits::Block>::Header: std::panic::UnwindSafe
            + std::panic::RefUnwindSafe,
        __SR_API_BLOCK__::Header: std::panic::UnwindSafe + std::panic::RefUnwindSafe,
    {
        fn __runtime_api_internal_call_api_at(
            &self,
            at: <__SR_API_BLOCK__ as self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::BlockT>::Hash,
            context: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ExecutionContext,
            params: std::vec::Vec<u8>,
            fn_name: &dyn Fn(
                self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::RuntimeVersion,
            ) -> &'static str,
        ) -> std::result::Result<
            std::vec::Vec<u8>,
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ApiError,
        > {
            if *std::cell::RefCell::borrow(&self.commit_on_success) {
                self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::OverlayedChanges::start_transaction(
                    &mut std::cell::RefCell::borrow_mut(&self.changes),
                );
            }
            let res = (|| {
                let version = self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt::<
                    __SR_API_BLOCK__,
                >::runtime_version_at(self.call, at)?;
                let params = self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAtParams {
                    at,
                    function: (*fn_name)(version),
                    arguments: params,
                    overlayed_changes: &self.changes,
                    storage_transaction_cache: &self.storage_transaction_cache,
                    context,
                    recorder: &self.recorder,
                };
                self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt::<
                    __SR_API_BLOCK__,
                >::call_api_at(self.call, params)
            })();
            self.commit_or_rollback(std::result::Result::is_ok(&res));
            res
        }
    }
    #[cfg(any(feature = "std", test))]
    impl<
        __SR_API_BLOCK__: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::BlockT
            + std::panic::UnwindSafe + std::panic::RefUnwindSafe,
        RuntimeApiImplCall: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt<
                __SR_API_BLOCK__,
            > + 'static,
    > sp_api::Metadata<__SR_API_BLOCK__>
    for RuntimeApiImpl<__SR_API_BLOCK__, RuntimeApiImplCall>
    where
        RuntimeApiImplCall::StateBackend: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::StateBackend<
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::HashFor<
                __SR_API_BLOCK__,
            >,
        >,
        &'static RuntimeApiImplCall: Send,
        OpaqueMetadata: std::panic::UnwindSafe + std::panic::RefUnwindSafe,
        __SR_API_BLOCK__::Header: std::panic::UnwindSafe + std::panic::RefUnwindSafe,
    {
        fn __runtime_api_internal_call_api_at(
            &self,
            at: <__SR_API_BLOCK__ as self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::BlockT>::Hash,
            context: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ExecutionContext,
            params: std::vec::Vec<u8>,
            fn_name: &dyn Fn(
                self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::RuntimeVersion,
            ) -> &'static str,
        ) -> std::result::Result<
            std::vec::Vec<u8>,
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ApiError,
        > {
            if *std::cell::RefCell::borrow(&self.commit_on_success) {
                self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::OverlayedChanges::start_transaction(
                    &mut std::cell::RefCell::borrow_mut(&self.changes),
                );
            }
            let res = (|| {
                let version = self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt::<
                    __SR_API_BLOCK__,
                >::runtime_version_at(self.call, at)?;
                let params = self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAtParams {
                    at,
                    function: (*fn_name)(version),
                    arguments: params,
                    overlayed_changes: &self.changes,
                    storage_transaction_cache: &self.storage_transaction_cache,
                    context,
                    recorder: &self.recorder,
                };
                self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt::<
                    __SR_API_BLOCK__,
                >::call_api_at(self.call, params)
            })();
            self.commit_or_rollback(std::result::Result::is_ok(&res));
            res
        }
    }
    #[cfg(any(feature = "std", test))]
    impl<
        __SR_API_BLOCK__: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::BlockT
            + std::panic::UnwindSafe + std::panic::RefUnwindSafe,
        RuntimeApiImplCall: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt<
                __SR_API_BLOCK__,
            > + 'static,
    > frame_support::interface::Interface<__SR_API_BLOCK__, InterfaceView>
    for RuntimeApiImpl<__SR_API_BLOCK__, RuntimeApiImplCall>
    where
        RuntimeApiImplCall::StateBackend: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::StateBackend<
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::HashFor<
                __SR_API_BLOCK__,
            >,
        >,
        &'static RuntimeApiImplCall: Send,
        InterfaceView: std::panic::UnwindSafe + std::panic::RefUnwindSafe,
        ViewResult<Vec<u8>>: std::panic::UnwindSafe + std::panic::RefUnwindSafe,
        __SR_API_BLOCK__::Header: std::panic::UnwindSafe + std::panic::RefUnwindSafe,
    {
        fn __runtime_api_internal_call_api_at(
            &self,
            at: <__SR_API_BLOCK__ as self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::BlockT>::Hash,
            context: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ExecutionContext,
            params: std::vec::Vec<u8>,
            fn_name: &dyn Fn(
                self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::RuntimeVersion,
            ) -> &'static str,
        ) -> std::result::Result<
            std::vec::Vec<u8>,
            self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ApiError,
        > {
            if *std::cell::RefCell::borrow(&self.commit_on_success) {
                self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::OverlayedChanges::start_transaction(
                    &mut std::cell::RefCell::borrow_mut(&self.changes),
                );
            }
            let res = (|| {
                let version = self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt::<
                    __SR_API_BLOCK__,
                >::runtime_version_at(self.call, at)?;
                let params = self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAtParams {
                    at,
                    function: (*fn_name)(version),
                    arguments: params,
                    overlayed_changes: &self.changes,
                    storage_transaction_cache: &self.storage_transaction_cache,
                    context,
                    recorder: &self.recorder,
                };
                self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::CallApiAt::<
                    __SR_API_BLOCK__,
                >::call_api_at(self.call, params)
            })();
            self.commit_or_rollback(std::result::Result::is_ok(&res));
            res
        }
    }
    const RUNTIME_API_VERSIONS: self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::ApisVec = ::sp_version::sp_std::borrow::Cow::Borrowed(
        &[
            (sp_api::runtime_decl_for_Core::ID, sp_api::runtime_decl_for_Core::VERSION),
            (
                sp_api::runtime_decl_for_Metadata::ID,
                sp_api::runtime_decl_for_Metadata::VERSION,
            ),
            (
                frame_support::interface::runtime_decl_for_Interface::ID,
                frame_support::interface::runtime_decl_for_Interface::VERSION,
            ),
        ],
    );
    const _: () = {};
    const _: () = {};
    const _: () = {};
    pub mod api {
        use super::*;
        #[cfg(feature = "std")]
        pub fn dispatch(
            method: &str,
            mut __sp_api__input_data: &[u8],
        ) -> Option<Vec<u8>> {
            match method {
                "Core_version" => {
                    Some(
                        self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::Encode::encode(
                            &{
                                let (): () = match self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::DecodeLimit::decode_all_with_depth_limit(
                                    self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::MAX_EXTRINSIC_DEPTH,
                                    &mut __sp_api__input_data,
                                ) {
                                    Ok(res) => res,
                                    Err(e) => {
                                        ::core::panicking::panic_fmt(
                                            format_args!(
                                                "Bad input data provided to {0}: {1}", "version", e
                                            ),
                                        );
                                    }
                                };
                                #[allow(deprecated)]
                                <MockRuntime as sp_api::runtime_decl_for_Core::Core<
                                    Block,
                                >>::version()
                            },
                        ),
                    )
                }
                "Core_execute_block" => {
                    Some(
                        self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::Encode::encode(
                            &{
                                let (block): (Block) = match self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::DecodeLimit::decode_all_with_depth_limit(
                                    self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::MAX_EXTRINSIC_DEPTH,
                                    &mut __sp_api__input_data,
                                ) {
                                    Ok(res) => res,
                                    Err(e) => {
                                        ::core::panicking::panic_fmt(
                                            format_args!(
                                                "Bad input data provided to {0}: {1}", "execute_block", e
                                            ),
                                        );
                                    }
                                };
                                #[allow(deprecated)]
                                <MockRuntime as sp_api::runtime_decl_for_Core::Core<
                                    Block,
                                >>::execute_block(block)
                            },
                        ),
                    )
                }
                "Core_initialize_block" => {
                    Some(
                        self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::Encode::encode(
                            &{
                                let (header): (<Block as sp_runtime::traits::Block>::Header) = match self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::DecodeLimit::decode_all_with_depth_limit(
                                    self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::MAX_EXTRINSIC_DEPTH,
                                    &mut __sp_api__input_data,
                                ) {
                                    Ok(res) => res,
                                    Err(e) => {
                                        ::core::panicking::panic_fmt(
                                            format_args!(
                                                "Bad input data provided to {0}: {1}", "initialize_block", e
                                            ),
                                        );
                                    }
                                };
                                #[allow(deprecated)]
                                <MockRuntime as sp_api::runtime_decl_for_Core::Core<
                                    Block,
                                >>::initialize_block(&header)
                            },
                        ),
                    )
                }
                "Metadata_metadata" => {
                    Some(
                        self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::Encode::encode(
                            &{
                                let (): () = match self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::DecodeLimit::decode_all_with_depth_limit(
                                    self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::MAX_EXTRINSIC_DEPTH,
                                    &mut __sp_api__input_data,
                                ) {
                                    Ok(res) => res,
                                    Err(e) => {
                                        ::core::panicking::panic_fmt(
                                            format_args!(
                                                "Bad input data provided to {0}: {1}", "metadata", e
                                            ),
                                        );
                                    }
                                };
                                #[allow(deprecated)]
                                <MockRuntime as sp_api::runtime_decl_for_Metadata::Metadata<
                                    Block,
                                >>::metadata()
                            },
                        ),
                    )
                }
                "Interface_view" => {
                    Some(
                        self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::Encode::encode(
                            &{
                                let (view): (InterfaceView) = match self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::DecodeLimit::decode_all_with_depth_limit(
                                    self::sp_api_hidden_includes_IMPL_RUNTIME_APIS::sp_api::MAX_EXTRINSIC_DEPTH,
                                    &mut __sp_api__input_data,
                                ) {
                                    Ok(res) => res,
                                    Err(e) => {
                                        ::core::panicking::panic_fmt(
                                            format_args!(
                                                "Bad input data provided to {0}: {1}", "view", e
                                            ),
                                        );
                                    }
                                };
                                #[allow(deprecated)]
                                <MockRuntime as frame_support::interface::runtime_decl_for_Interface::Interface<
                                    Block,
                                    InterfaceView,
                                >>::view(view)
                            },
                        ),
                    )
                }
                _ => None,
            }
        }
    }
}
