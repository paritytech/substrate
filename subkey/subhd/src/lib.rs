// -*- mode: rust; -*-
//
// This file is part of subhd, substrate.
// Copyright (c) 2017-2019 Chester Li and extropies.com
// See LICENSE for licensing information.
//
// Authors:
// - Chester Li<chester@lichester.com>

//! hd wallet layer for subkey
extern crate solo;
extern crate hex_view;
use hex_view::HexView;

use primitives::{sr25519,sr25519::{ Signature,Public}};
use solo::{wk_getpub,wk_sign,wk_generate,wk_format,wk_import};
/// Error define
/// DeviceNotfound: device not connected
/// DeviceNotInit: empty device, generate or import first
/// DeviceError: general error of command
/// TODO: give detail error
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum HDWalletError {
    DeviceNotfound,
    DeviceNotInit,
    DeviceError
}
/// seed type
type Seed = [u8; 32];
/// subhd Result
pub type HDWalleResult<T> = Result<T, HDWalletError>;
/// struct device
pub struct HDDevice;
/// method of subhd
pub trait HDwallet{
    /// get public key
    /// Address in defualt return
    /// .into make it into public key
    fn hd_getpub(&self) ->  HDWalleResult<Public>;
    /// sign the message
    fn hd_sign(&self,message:&[u8]) -> HDWalleResult<Signature>;
    /// generate keypair and return seed
    fn hd_generate(&self) -> HDWalleResult<Seed>;
    /// import seed
    fn hd_import(&self,seed:&[u8]) -> HDWalleResult<()>;
    /// clear the device to empty
    fn hd_format(&self) -> HDWalleResult<()>;
    /// format seed hex string
    fn to_hex(&self,data:&[u8]) -> String;
}

/// implement of methods
impl HDwallet for HDDevice {
    /// get public key
    /// Address in defualt return
    /// .into make it into public key
    fn hd_getpub(&self) ->  HDWalleResult<Public>{
        let mut pk:[u8;32] = [0u8;32];
        let rv = wk_getpub(&mut pk);
        if rv==242{
            return Err(HDWalletError::DeviceNotInit);
        }else if rv!=0{
            return Err(HDWalletError::DeviceNotfound);
        }else if rv==0{
            Ok(sr25519::Public::from_raw(pk))
        }else{
            return Err(HDWalletError::DeviceError);
        }
    }
    /// sign the message
    fn hd_sign(&self,message:&[u8]) -> HDWalleResult<Signature>{
        let mut sig:[u8;64] = [0u8;64];
        let rv = wk_sign(message,&mut sig);
        if rv!=0 {
            return Err(HDWalletError::DeviceError);
        }
        Ok(sr25519::Signature::from_raw(sig))
    }
    /// generate keypair and return seed
    fn hd_generate(&self) -> HDWalleResult<Seed>{
        let mut seed:[u8;32] = [0u8;32];
        let rv = wk_generate(&mut seed);
        if rv!=0 {
            return Err(HDWalletError::DeviceError);
        }
        Ok(seed)
    }
    /// clear the device to empty
    fn hd_format(&self) -> HDWalleResult<()>{
        let rv = wk_format();
        if rv!=0 {
            return Err(HDWalletError::DeviceError);
        }
        Ok(())
    }
    /// import seed 
    fn hd_import(&self,seed:&[u8]) -> HDWalleResult<()>{
        let rv = wk_import(seed);
        if rv!=0 {
            return Err(HDWalletError::DeviceError);
        }
        Ok(())
    }
    /// format seed hex string
    fn to_hex(&self,data:&[u8]) -> String{
         format!("{:x}", HexView::from(&data[..]))
    }
}
