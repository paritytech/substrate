// -*- mode: rust; -*-
//
// This file is part of subhd/solo, substrate.
// Copyright (c) 2017-2019 Chester Li and extropies.com
// See LICENSE for licensing information.
//
// Authors:
// - Chester Li<chester@lichester.com>

//! C API to RUST for solo

extern {
    fn solo_pubkey(pk:*mut u8) -> u32;
    fn solo_sign(message: *const u8, len: usize, sig:*mut u8) -> u32;
    fn solo_generate(seed:*mut u8) -> u32;
    fn solo_format() -> u32;
    fn solo_import(seed:*const u8, len:usize) -> u32;
}

pub fn wk_getpub(pk:&mut [u8]) -> u32 {
    unsafe { solo_pubkey(pk.as_mut_ptr()) }

}

pub fn wk_sign(message:&[u8], sig:&mut [u8]) -> u32 {
    unsafe { solo_sign(message.as_ptr(),message.len(),sig.as_mut_ptr()) }
}

pub fn wk_generate(seed:&mut [u8]) -> u32 {
    unsafe { solo_generate(seed.as_mut_ptr()) }
}

pub fn wk_format() -> u32{
    unsafe { solo_format() }
}

pub fn wk_import(seed:&[u8]) -> u32 {
     unsafe { solo_import(seed.as_ptr(),seed.len()) }
}


