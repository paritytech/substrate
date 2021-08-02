// Copyright (C) 2021 Mangata team
#![cfg_attr(not(feature = "std"), no_std)]

sp_api::decl_runtime_apis! {
    pub trait RandomSeedApi{
        fn get_seed() -> pallet_random_seed::SeedType;
    }
}
