// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! hd wallet layer for subkey
use hex_view::HexView;

use primitives::{sr25519, sr25519::{ Signature,Public}};
use wookong_solo::{wk_getpub, wk_sign, wk_generate, wk_format, wk_import};
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
    fn hd_sign(&self, message:&[u8]) -> HDWalleResult<Signature>;
    /// generate keypair and return seed
    fn hd_generate(&self) -> HDWalleResult<Seed>;
    /// import seed
    fn hd_import(&self, seed:&[u8]) -> HDWalleResult<()>;
    /// clear the device to empty
    fn hd_format(&self) -> HDWalleResult<()>;
    /// format seed hex string
    fn to_hex(&self, data:&[u8]) -> String;
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
    fn hd_sign(&self, message:&[u8]) -> HDWalleResult<Signature>{
        let mut sig:[u8;64] = [0u8;64];
        let rv = wk_sign(message, &mut sig);
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
    fn hd_import(&self, seed:&[u8]) -> HDWalleResult<()>{
        let rv = wk_import(seed);
        if rv!=0 {
            return Err(HDWalletError::DeviceError);
        }
        Ok(())
    }
    /// format seed hex string
    fn to_hex(&self, data:&[u8]) -> String{
         format!("{:x}", HexView::from(&data[..]))
    }
}
