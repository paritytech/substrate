// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! # Intel SGX Enclave Hello World

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use frame_support::{
	debug, decl_module, decl_storage, decl_event, decl_error,
	dispatch::DispatchResult,
	weights::Pays
};
use frame_system::{self as system, offchain, ensure_signed};
use frame_system::offchain::{SendSignedTransaction, Signer};
use sp_core::crypto::KeyTypeId;
use sp_runtime::{
	RuntimeDebug, print,
	offchain::http,
	transaction_validity::{TransactionValidity, TransactionSource}
};
use sp_std::vec::Vec;
use sp_std::*;

#[cfg(test)]
mod tests;

/// Defines application identifier for crypto keys of this module.
pub const KEY_TYPE: KeyTypeId = KeyTypeId(*b"sgx!");

pub mod crypto {
	use crate::KEY_TYPE;
	use sp_core::sr25519::Signature as Sr25519Signature;
	use sp_runtime::{
		app_crypto::{app_crypto, sr25519},
		traits::Verify,
		MultiSignature, MultiSigner,
	};

	app_crypto!(sr25519, KEY_TYPE);

	pub struct TestAuthId;
	// implemented for ocw-runtime
	impl frame_system::offchain::AppCrypto<MultiSigner, MultiSignature> for TestAuthId {
		type RuntimeAppPublic = Public;
		type GenericSignature = sp_core::sr25519::Signature;
		type GenericPublic = sp_core::sr25519::Public;
	}

	// implemented for mock runtime in test
	impl frame_system::offchain::AppCrypto<<Sr25519Signature as Verify>::Signer, Sr25519Signature>
		for TestAuthId
	{
		type RuntimeAppPublic = Public;
		type GenericSignature = sp_core::sr25519::Signature;
		type GenericPublic = sp_core::sr25519::Public;
	}
}

#[derive(Encode, Decode, Default, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct QuotingReport {
    pub cpusvn: [u8; 16],
    pub miscselect: u32,
    pub attributes: [u8; 16],
	/// SHA 256 of enclave measurement
    pub mrenclave: [u8; 32],
	/// Enclave public signing key
    pub mrsigner: [u8; 32],
    pub isvprodid: u16,
    pub isvsvn: u16,
    pub reportdata: Vec<u8>,
}

impl QuotingReport {
	/// Poor man's deserialization based on
	/// https://api.trustedservices.intel.com/documents/sgx-attestation-api-spec.pdf 4.3.1
	pub fn from_bytes(bytes: &[u8]) -> Self {
		let mut cpusvn = [0_u8; 16];
		let mut miscselect = [0_u8; 4];
		let mut attributes = [0_u8; 16];
		let mut mrenclave = [0_u8; 32];
		let mut mrsigner = [0_u8; 32];
		let mut isvprodid = [0_u8; 2];
		let mut isvsvn = [0_u8; 2];
		let mut reportdata = vec![0_u8; 64];

		cpusvn.copy_from_slice(&bytes[48..48+16]);
		miscselect.copy_from_slice(&bytes[64..64+4]);
		attributes.copy_from_slice(&bytes[96..96+16]);
		mrenclave.copy_from_slice(&bytes[112..112+32]);
		mrsigner.copy_from_slice(&bytes[176..176+32]);
		isvprodid.copy_from_slice(&bytes[304..304+2]);
		isvsvn.copy_from_slice(&bytes[306..306+2]);
		reportdata.copy_from_slice(&bytes[368..368+64]);

		Self {
			cpusvn,
			miscselect: u32::from_le_bytes(miscselect),
			attributes,
			mrenclave,
			mrsigner,
			isvprodid: u16::from_le_bytes(isvprodid),
			isvsvn: u16::from_le_bytes(isvsvn),
			reportdata,
		}
	}
}

#[derive(Encode, Decode, Default, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct Enclave {
	pub quote: QuotingReport,
	pub address: Vec<u8>,
	pub timestamp: u64,
}

type EnclaveAddress = Vec<u8>;

/// This pallet's configuration trait
pub trait Trait: frame_system::Trait + offchain::CreateSignedTransaction<Call<Self>>  {
	/// The identifier type for an authority.
	type AuthorityId: offchain::AppCrypto<Self::Public, Self::Signature>;
    /// The overarching dispatch call type.
    type Call: From<Call<Self>>;
    /// The overarching event type.
    type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

decl_error! {
    pub enum Error for Module<T: Trait> {
		/// The enclave is already registrered
        EnclaveAlreadyRegistered,
		/// The enclave is not registrered
		EnclaveNotFound
    }
}

decl_storage! {
	trait Store for Module<T: Trait> as SgxHelloWorld {
		/// Enclaves that are verified (i.e, verified via remote attestation)
		VerifiedEnclaves get(fn verified_enclaves): map hasher(twox_64_concat) T::AccountId => Enclave;
		/// Enclaves that are waiting to be verified
		UnverifiedEnclaves get(fn unverified_enclaves): Vec<(T::AccountId, EnclaveAddress)>;
		/// Waiting enclave calls
		WaitingEnclaveCalls get(fn waiting_calls): Vec<(T::AccountId, Vec<u8>)>;
	}
}

decl_event!(
	pub enum Event<T> where AccountId = <T as frame_system::Trait>::AccountId {
		EnclaveAdded(AccountId),
		EnclaveRemoved(AccountId),
		EnclaveCallDispatched(AccountId),
	}
);

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		/// Try to register an enclave.
		///
		/// The transaction has to be signed with the enclave's signing key to work
		#[weight = (100, Pays::No)]
		pub fn register_enclave(origin, url: Vec<u8>) -> DispatchResult {
			print("register_enclave");
			let sender = ensure_signed(origin)?;

			let mut unverified_enclaves = UnverifiedEnclaves::<T>::get();
			if <VerifiedEnclaves<T>>::contains_key(&sender) {
				Err(Error::<T>::EnclaveAlreadyRegistered.into())
			} else {
				match unverified_enclaves.binary_search_by(|(s, _)| s.cmp(&sender)) {
					Ok(_) => Err(Error::<T>::EnclaveAlreadyRegistered.into()),
					Err(idx) => {
						debug::info!("[intel sgx]: register unverified_encalve; who={:?} at address={:?}", sender, url);
						unverified_enclaves.insert(idx, (sender.clone(), url));
						UnverifiedEnclaves::<T>::put(unverified_enclaves);
						Ok(())
					}
				}
			}
		}

		/// Try to deregister an enclave.
		///
		/// The transaction has to be signed with the enclave's signing key to work
		#[weight = (100, Pays::No)]
		pub fn deregister_enclave(origin) -> DispatchResult {
			let enclave = ensure_signed(origin)?;
			if <VerifiedEnclaves<T>>::contains_key(&enclave) {
				debug::info!("[intel sgx]: deregister who={:?}", enclave);
				<VerifiedEnclaves<T>>::remove(enclave.clone());
				Self::deposit_event(RawEvent::EnclaveRemoved(enclave));
				Ok(())
			} else {
				Err(Error::<T>::EnclaveNotFound.into())
			}
		}

		// TODO: This should pay fee workaround in `substrate-subxt` because
		// `TreasuryEvents` are not decoded properly
		#[weight = (100, Pays::No)]
		pub fn call_enclave(
			origin,
			enclave: T::AccountId,
			xt: Vec<u8>
		) -> DispatchResult {
			let _who = ensure_signed(origin)?;
			if <VerifiedEnclaves<T>>::contains_key(&enclave) {
				let mut waiting_calls = <WaitingEnclaveCalls<T>>::get();
				waiting_calls.push((enclave, xt));
				<WaitingEnclaveCalls<T>>::put(waiting_calls);
				Ok(())
			} else {
				Err(Error::<T>::EnclaveNotFound.into())
			}
		}

		#[weight = (100, Pays::No)]
		fn enclave_call_dispatched(origin, waiting_call: (T::AccountId, Vec<u8>)) -> DispatchResult {
			let _who = ensure_signed(origin)?;
			let mut waiting_calls = <WaitingEnclaveCalls<T>>::get();
			debug::info!("[intel sgx]: attempt to dispatch enclave call who={:?} with payload={:?}", waiting_call.0, waiting_call.1);
			match waiting_calls.binary_search(&waiting_call) {
				Ok(idx) => {
					waiting_calls.remove(idx);
					<WaitingEnclaveCalls<T>>::put(waiting_calls);
					Self::deposit_event(RawEvent::EnclaveCallDispatched(waiting_call.0));
					Ok(())
				}
				Err(_) => {
					Err(Error::<T>::EnclaveNotFound.into())
				}
			}
		}

		#[weight = (100, Pays::No)]
		fn prune_unverified_enclaves(origin) -> DispatchResult {
			let _who = ensure_signed(origin)?;
			<UnverifiedEnclaves<T>>::kill();
			Ok(())
		}

		#[weight = (100, Pays::No)]
		fn register_verified_enclave(origin, enclave_id: T::AccountId, enclave: Enclave) -> DispatchResult {
			let _who = ensure_signed(origin)?;
			debug::info!("[intel sgx]: register_verified_enclave who={:?} with meta={:?}", enclave_id, enclave);
			<VerifiedEnclaves<T>>::insert(enclave_id.clone(), enclave);
			Self::deposit_event(RawEvent::EnclaveAdded(enclave_id));
			Ok(())
		}

		fn deposit_event() = default;

		/// Offchain Worker entry point.
		//
		// TODO: use the offchain worker to re-verify the "trusted enclaves"
		// every x block or maybe could be done in `on_initialize` or `on_finalize`
		fn offchain_worker(block_number: T::BlockNumber) {
			let waiting_enclaves = <UnverifiedEnclaves<T>>::get();
			if !waiting_enclaves.is_empty() {
				Self::remote_attest_unverified_enclaves().unwrap();
			}

			let waiting_calls = <WaitingEnclaveCalls<T>>::get();
			if !waiting_calls.is_empty() {
				Self::dispatch_waiting_calls().unwrap();
			}

			// Re-verify "verified enclaves" at least once every hour
			// An enclave might get revoked or vulnerabilities might get detected
			//
			// Assuming the block production time is 1-20 seconds
			if block_number % 2000.into() == 0.into() {
				// TODO: implement me
			}
		}
	}
}

impl<T: Trait> Module<T> {
	fn remote_attest_unverified_enclaves() -> Result<(), &'static str> {
		let signer = Signer::<T, T::AuthorityId>::all_accounts();
		if !signer.can_sign() {
			return Err("No local accounts available. Consider adding one via `author_insertKey` RPC with keytype \"sgx!\"");
		}

		let mut verified = Vec::new();

		for (enclave_sign, enclave_addr) in <UnverifiedEnclaves<T>>::get() {
			let qe = match Self::send_ra_request(&enclave_sign, &enclave_addr) {
				Ok(qe) => qe,
				Err(e) => {
					debug::warn!("[enclave]; request failed: {}. Enclave might be down; ignoring", e);
					continue
				}
			};

			let enclave = Enclave {
				address: enclave_addr.clone(),
				quote: QuotingReport::from_bytes(&qe),
				timestamp: sp_io::offchain::timestamp().unix_millis()
			};
			debug::info!("[intel sgx] received quoting_report: {:?}", enclave.quote);
			let vr = match Self::get_ias_verification_report(&qe) {
				Ok(vr) => vr,
				Err(e) => {
					debug::warn!("[IAS]; request failed with error: {}", e);
					continue
				}
			};

			debug::info!("[intel sgx] received ias_verification_report: {:?}", vr);
			debug::warn!("[intel sgx] ias_verification_report is not used yet");
			verified.push((enclave_sign, enclave))
		}


		signer.send_signed_transaction(|_account| {
			Call::prune_unverified_enclaves()
		});

		for (enclave_sign, enclave) in verified {
			signer.send_signed_transaction(|_account| {
				Call::register_verified_enclave(enclave_sign.clone(), enclave.clone())
			});
		}

		Ok(())
	}

	fn dispatch_waiting_calls() -> Result<(), &'static str> {
		let signer = Signer::<T, T::AuthorityId>::all_accounts();
		if !signer.can_sign() {
			return Err("No local accounts available. Consider adding one via `author_insertKey` RPC with keytype \"sgx!\"");
		}

		let mut dispatched = Vec::new();

		for (enclave_id, xt) in <WaitingEnclaveCalls<T>>::get() {
			if !<VerifiedEnclaves<T>>::contains_key(&enclave_id) {
				continue;
			}
			let enclave = <VerifiedEnclaves<T>>::get(&enclave_id);
			let mut full_address = Vec::new();
			full_address.extend(&enclave.address);
			full_address.extend("/enclave_call".as_bytes());
			let enclave_addr = sp_std::str::from_utf8(&full_address).unwrap();
			debug::info!("[intel sgx]: sending enclave_call to={:?} at address={:?}", enclave_id, enclave_addr);
			if let Ok(Ok(response)) = http::Request::post(&enclave_addr, vec![&xt])
				.add_header("substrate_sgx", "1.0")
				.send()
				.and_then(|r| Ok(r.wait())) {
					dispatched.push((enclave_id, xt));
					let body: Vec<u8> = response.body().collect();
					debug::info!("dispatch_waiting_call response: {:?}", body);
				}
		}

		for (enclave, xt) in dispatched {
			signer.send_signed_transaction(|_account| {
				Call::enclave_call_dispatched((enclave.clone(), xt.clone()))
			});
		}
		Ok(())
	}

	fn send_ra_request(signer: &T::AccountId, enclave_addr: &[u8]) -> Result<Vec<u8>, &'static str> {
		let mut full_address: Vec<u8> = Vec::new();
		full_address.extend(enclave_addr);
		full_address.extend("/quoting_report".as_bytes());
		let enclave_addr = sp_std::str::from_utf8(&full_address).map_err(|_e| "enclave address must be valid utf8")?;
		let body = vec![b"remote_attest\r\n"];
		debug::info!("[intel sgx]: sending remote attestion request to enclave={:?} at address={:?}", signer, enclave_addr);
		let pending = http::Request::post(&enclave_addr, body)
			.add_header("substrate_sgx", "1.0")
			.send()
			.unwrap();
		let response = pending.wait().expect("http IO error");
		Ok(response.body().collect())
	}

	// https://api.trustedservices.intel.com/documents/sgx-attestation-api-spec.pdf
	fn get_ias_verification_report(quote: &[u8]) -> Result<Vec<u8>, &'static str> {
		const IAS_REPORT_URL: &str = "https://api.trustedservices.intel.com/sgx/dev/attestation/v4/report";
		const API_KEY: &str = "e9589de0dfe5482588600a73d08b70f6";

		// { "isvEnclaveQuote": "<base64 encoded quote>" }
		let encoded_quote = base64::encode(&quote);
		let mut body = Vec::new();
		body.push("{\"isvEnclaveQuote\":");
		body.push("\"");
		body.push(&encoded_quote);
		body.push("\"}");

		let pending = http::Request::post(IAS_REPORT_URL, body)
			.add_header("Content-Type", "application/json")
			.add_header("Ocp-Apim-Subscription-Key", API_KEY)
			.send()
			.unwrap();

		let response = pending.wait().expect("http IO error");
		if response.code == 200 {
			Ok(response.body().collect())
		} else {
			Err("Intel IAS error")
		}
	}
}

#[allow(deprecated)] // ValidateUnsigned
impl<T: Trait> frame_support::unsigned::ValidateUnsigned for Module<T> {
	type Call = Call<T>;

	fn validate_unsigned(
		_source: TransactionSource,
		_call: &Self::Call,
	) -> TransactionValidity {
		todo!("implement when sgx_hello_world is using unsigned transactions");
	}
}
