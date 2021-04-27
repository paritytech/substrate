// Snippets of code for inspiration.



//! Run `cargo doc --package pallet-example-offchain-worker --open` to view this module's
//! documentation.


//decl_storage! {
//	trait Store for Module<T: Trait> as ExampleOffchainWorker {
//		/// A vector of recently submitted prices.
//		///
//		/// This is used to calculate average price, should have bounded size.
//		Prices get(fn prices): Vec<u32>;
//		/// Defines the block when next unsigned transaction will be accepted.
//		///
//		/// To prevent spam of unsigned (and unpayed!) transactions on the network,
//		/// we only allow one transaction every `T::UnsignedInterval` blocks.
//		/// This storage entry defines when new transaction is going to be accepted.
//		NextUnsignedAt get(fn next_unsigned_at): T::BlockNumber;
//	}
//}



/// Payload used by this example crate to hold price
/// data required to submit a transaction.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct PricePayload<Public, BlockNumber> {
	block_number: BlockNumber,
	price: u32,
	public: Public,
}

impl<T: SigningTypes> SignedPayload<T> for PricePayload<T::Public, T::BlockNumber> {
	fn public(&self) -> T::Public {
		self.public.clone()
	}
}





// Adding on-chain transactions.
pub struct Module …

		/// Submit new price to the list.
		///
		/// This method is a public function of the module and can be called from within
		/// a transaction. It appends given `price` to current list of prices.
		/// In our example the `offchain worker` will create, sign & submit a transaction that
		/// calls this function passing the price.
		///
		/// The transaction needs to be signed (see `ensure_signed`) check, so that the caller
		/// pays a fee to execute it.
		/// This makes sure that it's not easy (or rather cheap) to attack the chain by submitting
		/// excesive transactions, but note that it doesn't ensure the price oracle is actually
		/// working and receives (and provides) meaningful data.
		/// This example is not focused on correctness of the oracle itself, but rather its
		/// purpose is to showcase offchain worker capabilities.
        /// 
        /// Use with:
        ///   Call::submit_test_data("Hello World data".as_bytes().to_vec())
		#[weight = 0]
		pub fn submit_test_data(origin, test_str: Vec<u8>) -> DispatchResult {
			// Retrieve sender of the transaction.
			let who = ensure_signed(origin)?;
			// Add the price to the on-chain list.
			Self::add_test_data_event(who, test_str);
			Ok(())
		}

		/// Submit new price to the list via unsigned transaction.
		///
		/// Works exactly like the `submit_price` function, but since we allow sending the
		/// transaction without a signature, and hence without paying any fees,
		/// we need a way to make sure that only some transactions are accepted.
		/// This function can be called only once every `T::UnsignedInterval` blocks.
		/// Transactions that call that function are de-duplicated on the pool level
		/// via `validate_unsigned` implementation and also are rendered invalid if
		/// the function has already been called in current "session".
		///
		/// It's important to specify `weight` for unsigned calls as well, because even though
		/// they don't charge fees, we still don't want a single block to contain unlimited
		/// number of such transactions.
		///
		/// This example is not focused on correctness of the oracle itself, but rather its
		/// purpose is to showcase offchain worker capabilities.
		#[weight = 0]
		pub fn submit_price_unsigned(origin, _block_number: T::BlockNumber, price: u32)
			-> DispatchResult
		{
			// This ensures that the function can only be called via unsigned transaction.
			ensure_none(origin)?;
			// Add the price to the on-chain list, but mark it as coming from an empty address.
			Self::add_price(Default::default(), price);
			// now increment the block number at which we expect next unsigned transaction.
			let current_block = <system::Module<T>>::block_number();
			<NextUnsignedAt<T>>::put(current_block + T::UnsignedInterval::get());
			Ok(())
		}

		#[weight = 0]
		pub fn submit_price_unsigned_with_signed_payload(
			origin,
			price_payload: PricePayload<T::Public, T::BlockNumber>,
			_signature: T::Signature,
		) -> DispatchResult {
			// This ensures that the function can only be called via unsigned transaction.
			ensure_none(origin)?;
			// Add the price to the on-chain list, but mark it as coming from an empty address.
			Self::add_price(Default::default(), price_payload.price);
			// now increment the block number at which we expect next unsigned transaction.
			let current_block = <system::Module<T>>::block_number();
			<NextUnsignedAt<T>>::put(current_block + T::UnsignedInterval::get());
			Ok(())
		}



// In worker code.
fn offchain_worker(block_number: T::BlockNumber) {

			// Since off-chain workers are just part of the runtime code, they have direct access
			// to the storage and other included pallets.
			//
			// We can easily import `frame_system` and retrieve a block hash of the parent block.
			let parent_hash = <system::Module<T>>::block_hash(block_number - 1u32.into());
			debug::debug!("Current block: {:?} (parent hash: {:?})", block_number, parent_hash);

			// It's a good practice to keep `fn offchain_worker()` function minimal, and move most
			// of the code to separate `impl` block.
			// Here we call a helper function to calculate current average price.
			// This function reads storage entries of the current state.
			let average: Option<u32> = Self::average_price();
			debug::debug!("Current price: {:?}", average);

			// For this example we are going to send both signed and unsigned transactions
			// depending on the block number.
			// Usually it's enough to choose one or the other.
			let should_send = Self::choose_transaction_type(block_number);
			let res = match should_send {
				TransactionType::Signed => Self::fetch_price_and_send_signed(),
				TransactionType::UnsignedForAny => Self::fetch_price_and_send_unsigned_for_any_account(block_number),
				TransactionType::UnsignedForAll => Self::fetch_price_and_send_unsigned_for_all_accounts(block_number),
				TransactionType::Raw => Self::fetch_price_and_send_raw_unsigned(block_number),
				TransactionType::None => Ok(()),
			};



enum TransactionType {
    Signed,
    UnsignedForAny,
    UnsignedForAll,
    Raw,
    None,
}



impl<T: Trait> Module<T> {
	fn choose_transaction_type(block_number: T::BlockNumber) -> TransactionType {
		/// A friendlier name for the error that is going to be returned in case we are in the grace
		/// period.
		const RECENTLY_SENT: () = ();

		// Start off by creating a reference to Local Storage value.
		// Since the local storage is common for all offchain workers, it's a good practice
		// to prepend your entry with the module name.
		let val = StorageValueRef::persistent(b"example_ocw::last_send");
		// The Local Storage is persisted and shared between runs of the offchain workers,
		// and offchain workers may run concurrently. We can use the `mutate` function, to
		// write a storage entry in an atomic fashion. Under the hood it uses `compare_and_set`
		// low-level method of local storage API, which means that only one worker
		// will be able to "acquire a lock" and send a transaction if multiple workers
		// happen to be executed concurrently.
		let res = val.mutate(|last_send: Option<Option<T::BlockNumber>>| {
			// We match on the value decoded from the storage. The first `Option`
			// indicates if the value was present in the storage at all,
			// the second (inner) `Option` indicates if the value was succesfuly
			// decoded to expected type (`T::BlockNumber` in our case).
			match last_send {
				// If we already have a value in storage and the block number is recent enough
				// we avoid sending another transaction at this time.
				Some(Some(block)) if block_number < block + T::GracePeriod::get() => {
					Err(RECENTLY_SENT)
				},
				// In every other case we attempt to acquire the lock and send a transaction.
				_ => Ok(block_number)
			}
		});

		// The result of `mutate` call will give us a nested `Result` type.
		// The first one matches the return of the closure passed to `mutate`, i.e.
		// if we return `Err` from the closure, we get an `Err` here.
		// In case we return `Ok`, here we will have another (inner) `Result` that indicates
		// if the value has been set to the storage correctly - i.e. if it wasn't
		// written to in the meantime.
		match res {
			// The value has been set correctly, which means we can safely send a transaction now.
			Ok(Ok(block_number)) => {
				// Depending if the block is even or odd we will send a `Signed` or `Unsigned`
				// transaction.
				// Note that this logic doesn't really guarantee that the transactions will be sent
				// in an alternating fashion (i.e. fairly distributed). Depending on the execution
				// order and lock acquisition, we may end up for instance sending two `Signed`
				// transactions in a row. If a strict order is desired, it's better to use
				// the storage entry for that. (for instance store both block number and a flag
				// indicating the type of next transaction to send).
				let transaction_type = block_number % 3u32.into();
				if transaction_type == Zero::zero() { TransactionType::Signed }
				else if transaction_type == T::BlockNumber::from(1u32) { TransactionType::UnsignedForAny }
				else if transaction_type == T::BlockNumber::from(2u32) { TransactionType::UnsignedForAll }
				else { TransactionType::Raw }
			},
			// We are in the grace period, we should not send a transaction this time.
			Err(RECENTLY_SENT) => TransactionType::None,
			// We wanted to send a transaction, but failed to write the block number (acquire a
			// lock). This indicates that another offchain worker that was running concurrently
			// most likely executed the same logic and succeeded at writing to storage.
			// Thus we don't really want to send the transaction, knowing that the other run
			// already did.
			Ok(Err(_)) => TransactionType::None,
		}
	}

	fn fetch_price_and_send_signed() -> Result<(), &'static str> {
		let signer = Signer::<T, T::AuthorityId>::all_accounts();
		if !signer.can_sign() {
			return Err(
				"No local accounts available. Consider adding one via `author_insertKey` RPC."
			)?
		}
		// Make an external HTTP request to fetch the current price.
		// Note this call will block until response is received.
		let price = Self::fetch_price().map_err(|_| "Failed to fetch price")?;

		// Using `send_signed_transaction` associated type we create and submit a transaction
		// representing the call, we've just created.
		// Submit signed will return a vector of results for all accounts that were found in the
		// local keystore with expected `KEY_TYPE`.
		let results = signer.send_signed_transaction(
			|_account| {
				// Received price is wrapped into a call to `submit_price` public function of this pallet.
				// This means that the transaction, when executed, will simply call that function passing
				// `price` as an argument.
				Call::submit_price(price)
			}
		);

		for (acc, res) in &results {
			match res {
				Ok(()) => debug::info!("[{:?}] Submitted price of {} cents", acc.id, price),
				Err(e) => debug::error!("[{:?}] Failed to submit transaction: {:?}", acc.id, e),
			}
		}

		Ok(())
	}

	fn fetch_price_and_send_raw_unsigned(block_number: T::BlockNumber) -> Result<(), &'static str> {
		// Make sure we don't fetch the price if unsigned transaction is going to be rejected
		// anyway.
		let next_unsigned_at = <NextUnsignedAt<T>>::get();
		if next_unsigned_at > block_number {
			return Err("Too early to send unsigned transaction")
		}

		// Make an external HTTP request to fetch the current price.
		// Note this call will block until response is received.
		let price = Self::fetch_price().map_err(|_| "Failed to fetch price")?;

		// Received price is wrapped into a call to `submit_price_unsigned` public function of this
		// pallet. This means that the transaction, when executed, will simply call that function
		// passing `price` as an argument.
		let call = Call::submit_price_unsigned(block_number, price);

		// Now let's create a transaction out of this call and submit it to the pool.
		// Here we showcase two ways to send an unsigned transaction / unsigned payload (raw)
		//
		// By default unsigned transactions are disallowed, so we need to whitelist this case
		// by writing `UnsignedValidator`. Note that it's EXTREMELY important to carefuly
		// implement unsigned validation logic, as any mistakes can lead to opening DoS or spam
		// attack vectors. See validation logic docs for more details.
		//
		SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call.into())
			.map_err(|()| "Unable to submit unsigned transaction.")?;

		Ok(())
	}

	fn fetch_price_and_send_unsigned_for_any_account(block_number: T::BlockNumber) -> Result<(), &'static str> {
		// Make sure we don't fetch the price if unsigned transaction is going to be rejected
		// anyway.
		let next_unsigned_at = <NextUnsignedAt<T>>::get();
		if next_unsigned_at > block_number {
			return Err("Too early to send unsigned transaction")
		}

		// Make an external HTTP request to fetch the current price.
		// Note this call will block until response is received.
		let price = Self::fetch_price().map_err(|_| "Failed to fetch price")?;

		// -- Sign using any account
		let (_, result) = Signer::<T, T::AuthorityId>::any_account().send_unsigned_transaction(
			|account| PricePayload {
				price,
				block_number,
				public: account.public.clone()
			},
			|payload, signature| {
				Call::submit_price_unsigned_with_signed_payload(payload, signature)
			}
		).ok_or("No local accounts accounts available.")?;
		result.map_err(|()| "Unable to submit transaction")?;

		Ok(())
	}

	fn fetch_price_and_send_unsigned_for_all_accounts(block_number: T::BlockNumber) -> Result<(), &'static str> {
		// Make sure we don't fetch the price if unsigned transaction is going to be rejected
		// anyway.
		let next_unsigned_at = <NextUnsignedAt<T>>::get();
		if next_unsigned_at > block_number {
			return Err("Too early to send unsigned transaction")
		}

		// Make an external HTTP request to fetch the current price.
		// Note this call will block until response is received.
		let price = Self::fetch_price().map_err(|_| "Failed to fetch price")?;

		// -- Sign using all accounts
		let transaction_results = Signer::<T, T::AuthorityId>::all_accounts()
			.send_unsigned_transaction(
				|account| PricePayload {
					price,
					block_number,
					public: account.public.clone()
				},
				|payload, signature| {
					Call::submit_price_unsigned_with_signed_payload(payload, signature)
				}
			);
		for (_account_id, result) in transaction_results.into_iter() {
			if result.is_err() {
				return Err("Unable to submit transaction");
			}
		}

		Ok(())
	}


//	fn fetch_price() -> Result<u32, http::Error> {
//		// We want to keep the offchain worker execution time reasonable, so we set a hard-coded
//		// deadline to 2s to complete the external call.
//		// You can also wait idefinitely for the response, however you may still get a timeout
//		// coming from the host machine.
//		let deadline = sp_io::offchain::timestamp().add(Duration::from_millis(2_000));
//		// Initiate an external HTTP GET request.
//		// This is using high-level wrappers from `sp_runtime`, for the low-level calls that
//		// you can find in `sp_io`. The API is trying to be similar to `reqwest`, but
//		// since we are running in a custom WASM execution environment we can't simply
//		// import the library here.
//		let request = http::Request::get(
//			"https://min-api.cryptocompare.com/data/price?fsym=BTC&tsyms=USD"
//		);
//		// We set the deadline for sending of the request, note that awaiting response can
//		// have a separate deadline. Next we send the request, before that it's also possible
//		// to alter request headers or stream body content in case of non-GET requests.
//		let pending = request
//			.deadline(deadline)
//			.send()
//			.map_err(|_| http::Error::IoError)?;
//
//		// The request is already being processed by the host, we are free to do anything
//		// else in the worker (we can send multiple concurrent requests too).
//		// At some point however we probably want to check the response though,
//		// so we can block current thread and wait for it to finish.
//		// Note that since the request is being driven by the host, we don't have to wait
//		// for the request to have it complete, we will just not read the response.
//		let response = pending.try_wait(deadline)
//			.map_err(|_| http::Error::DeadlineReached)??;
//		// Let's check the status code before we proceed to reading the response.
//		if response.code != 200 {
//			debug::warn!("Unexpected status code: {}", response.code);
//			return Err(http::Error::Unknown);
//		}
//
//		// Next we want to fully read the response body and collect it to a vector of bytes.
//		// Note that the return object allows you to read the body in chunks as well
//		// with a way to control the deadline.
//		let body = response.body().collect::<Vec<u8>>();
//
//		// Create a str slice from the body.
//		let body_str = sp_std::str::from_utf8(&body).map_err(|_| {
//			debug::warn!("No UTF8 body");
//			http::Error::Unknown
//		})?;
//
//		let price = match Self::parse_price(body_str) {
//			Some(price) => Ok(price),
//			None => {
//				debug::warn!("Unable to extract price from the response: {:?}", body_str);
//				Err(http::Error::Unknown)
//			}
//		}?;
//
//		debug::warn!("Got price: {} cents", price);
//
//		Ok(price)
//	}

//	fn parse_price(price_str: &str) -> Option<u32> {
//		let val = lite_json::parse_json(price_str);
//		let price = val.ok().and_then(|v| match v {
//			JsonValue::Object(obj) => {
//				let mut chars = "USD".chars();
//				obj.into_iter()
//					.find(|(k, _)| k.iter().all(|k| Some(*k) == chars.next()))
//					.and_then(|v| match v.1 {
//						JsonValue::Number(number) => Some(number),
//						_ => None,
//					})
//			},
//			_ => None
//		})?;
//
//		let exp = price.fraction_length.checked_sub(2).unwrap_or(0);
//		Some(price.integer as u32 * 100 + (price.fraction / 10_u64.pow(exp)) as u32)
//	}

fn add_test_data_event(who: T::AccountId, test_str: Vec<u8>) {
    let s = match sp_std::str::from_utf8(&test_str) {
        Ok(v) => v,
        Err(e) => panic!("Invalid UTF-8 sequence: {}", e),
    };

    debug::info!("Adding Test Event: {}", s);

    Self::deposit_event(RawEvent::NewTestEvent(test_str, who));
}

//	fn average_price() -> Option<u32> {
//		let prices = Prices::get();
//		if prices.is_empty() {
//			None
//		} else {
//			Some(prices.iter().fold(0_u32, |a, b| a.saturating_add(*b)) / prices.len() as u32)
//		}
//	}

//	fn validate_transaction_parameters(
//		block_number: &T::BlockNumber,
//		new_price: &u32,
//	) -> TransactionValidity {
//		// Now let's check if the transaction has any chance to succeed.
//		let next_unsigned_at = <NextUnsignedAt<T>>::get();
//		if &next_unsigned_at > block_number {
//			return InvalidTransaction::Stale.into();
//		}
//		// Let's make sure to reject transactions from the future.
//		let current_block = <system::Module<T>>::block_number();
//		if &current_block < block_number {
//			return InvalidTransaction::Future.into();
//		}
//
//		// We prioritize transactions that are more far away from current average.
//		//
//		// Note this doesn't make much sense when building an actual oracle, but this example
//		// is here mostly to show off offchain workers capabilities, not about building an
//		// oracle.
//		let avg_price = Self::average_price()
//			.map(|price| if &price > new_price { price - new_price } else { new_price - price })
//			.unwrap_or(0);
//
//		ValidTransaction::with_tag_prefix("ExampleOffchainWorker")
//			// We set base priority to 2**20 and hope it's included before any other
//			// transactions in the pool. Next we tweak the priority depending on how much
//			// it differs from the current average. (the more it differs the more priority it
//			// has).
//			.priority(T::UnsignedPriority::get().saturating_add(avg_price as _))
//			// This transaction does not require anything else to go before into the pool.
//			// In theory we could require `previous_unsigned_at` transaction to go first,
//			// but it's not necessary in our case.
//			//.and_requires()
//			// We set the `provides` tag to be the same as `next_unsigned_at`. This makes
//			// sure only one transaction produced after `next_unsigned_at` will ever
//			// get to the transaction pool and will end up in the block.
//			// We can still have multiple transactions compete for the same "spot",
//			// and the one with higher priority will replace other one in the pool.
//			.and_provides(next_unsigned_at)
//			// The transaction is only valid for next 5 blocks. After that it's
//			// going to be revalidated by the pool.
//			.longevity(5)
//			// It's fine to propagate that transaction to other peers, which means it can be
//			// created even by nodes that don't produce blocks.
//			// Note that sometimes it's better to keep it for yourself (if you are the block
//			// producer), since for instance in some schemes others may copy your solution and
//			// claim a reward.
//			.propagate(true)
//			.build()
//	}
}
//
//#[allow(deprecated)] // ValidateUnsigned
//impl<T: Trait> frame_support::unsigned::ValidateUnsigned for Module<T> {
//	type Call = Call<T>;
//
//	/// Validate unsigned call to this module.
//	///
//	/// By default unsigned transactions are disallowed, but implementing the validator
//	/// here we make sure that some particular calls (the ones produced by offchain worker)
//	/// are being whitelisted and marked as valid.
//	fn validate_unsigned(
//		_source: TransactionSource,
//		call: &Self::Call,
//	) -> TransactionValidity {
//		// Firstly let's check that we call the right function.
//		if let Call::submit_price_unsigned_with_signed_payload(
//			ref payload, ref signature
//		) = call {
//			let signature_valid = SignedPayload::<T>::verify::<T::AuthorityId>(payload, signature.clone());
//			if !signature_valid {
//				return InvalidTransaction::BadProof.into();
//			}
//			Self::validate_transaction_parameters(&payload.block_number, &payload.price)
//		} else if let Call::submit_price_unsigned(block_number, new_price) = call {
//			Self::validate_transaction_parameters(block_number, new_price)
//		} else {
//			InvalidTransaction::Call.into()
//		}
//	}
//}




// Make types with Get trait.
parameter_types! {
	pub const UnsignedInterval: u64 = 128;
}


#[test]
fn should_submit_unsigned_transaction_on_chain_for_any_account() {
	const PHRASE: &str = "news slush supreme milk chapter athlete soap sausage put clutch what kitten";
	let (offchain, offchain_state) = testing::TestOffchainExt::new();
	let (pool, pool_state) = testing::TestTransactionPoolExt::new();

	let keystore = KeyStore::new();

	keystore.write().sr25519_generate_new(
		crate::crypto::Public::ID,
		Some(&format!("{}/hunter1", PHRASE))
	).unwrap();

	let mut t = sp_io::TestExternalities::default();
	t.register_extension(OffchainExt::new(offchain));
	t.register_extension(TransactionPoolExt::new(pool));
	t.register_extension(KeystoreExt(keystore.clone()));

	price_oracle_response(&mut offchain_state.write());

	let public_key = keystore.read()
		.sr25519_public_keys(crate::crypto::Public::ID)
		.get(0)
		.unwrap()
		.clone();

	let price_payload = PricePayload {
		block_number: 1,
		price: 15523,
		public: <Test as SigningTypes>::Public::from(public_key),
	};

	// let signature = price_payload.sign::<crypto::TestAuthId>().unwrap();
	t.execute_with(|| {
		// when
		Example::fetch_price_and_send_unsigned_for_any_account(1).unwrap();
		// then
		let tx = pool_state.write().transactions.pop().unwrap();
		let tx = Extrinsic::decode(&mut &*tx).unwrap();
		assert_eq!(tx.signature, None);
		if let Call::submit_price_unsigned_with_signed_payload(body, signature) = tx.call {
			assert_eq!(body, price_payload);

			let signature_valid = <PricePayload<
				<Test as SigningTypes>::Public,
				<Test as frame_system::Trait>::BlockNumber
					> as SignedPayload<Test>>::verify::<crypto::TestAuthId>(&price_payload, signature);

			assert!(signature_valid);
		}
	});
}

#[test]
fn should_submit_unsigned_transaction_on_chain_for_all_accounts() {
	const PHRASE: &str = "news slush supreme milk chapter athlete soap sausage put clutch what kitten";
	let (offchain, offchain_state) = testing::TestOffchainExt::new();
	let (pool, pool_state) = testing::TestTransactionPoolExt::new();

	let keystore = KeyStore::new();

	keystore.write().sr25519_generate_new(
		crate::crypto::Public::ID,
		Some(&format!("{}/hunter1", PHRASE))
	).unwrap();

	let mut t = sp_io::TestExternalities::default();
	t.register_extension(OffchainExt::new(offchain));
	t.register_extension(TransactionPoolExt::new(pool));
	t.register_extension(KeystoreExt(keystore.clone()));

	price_oracle_response(&mut offchain_state.write());

	let public_key = keystore.read()
		.sr25519_public_keys(crate::crypto::Public::ID)
		.get(0)
		.unwrap()
		.clone();

	let price_payload = PricePayload {
		block_number: 1,
		price: 15523,
		public: <Test as SigningTypes>::Public::from(public_key),
	};

	// let signature = price_payload.sign::<crypto::TestAuthId>().unwrap();
	t.execute_with(|| {
		// when
		Example::fetch_price_and_send_unsigned_for_all_accounts(1).unwrap();
		// then
		let tx = pool_state.write().transactions.pop().unwrap();
		let tx = Extrinsic::decode(&mut &*tx).unwrap();
		assert_eq!(tx.signature, None);
		if let Call::submit_price_unsigned_with_signed_payload(body, signature) = tx.call {
			assert_eq!(body, price_payload);

			let signature_valid = <PricePayload<
				<Test as SigningTypes>::Public,
				<Test as frame_system::Trait>::BlockNumber
					> as SignedPayload<Test>>::verify::<crypto::TestAuthId>(&price_payload, signature);

			assert!(signature_valid);
		}
	});
}

#[test]
fn should_submit_raw_unsigned_transaction_on_chain() {
	let (offchain, offchain_state) = testing::TestOffchainExt::new();
	let (pool, pool_state) = testing::TestTransactionPoolExt::new();

	let keystore = KeyStore::new();

	let mut t = sp_io::TestExternalities::default();
	t.register_extension(OffchainExt::new(offchain));
	t.register_extension(TransactionPoolExt::new(pool));
	t.register_extension(KeystoreExt(keystore));

	price_oracle_response(&mut offchain_state.write());

	t.execute_with(|| {
		// when
		Example::fetch_price_and_send_raw_unsigned(1).unwrap();
		// then
		let tx = pool_state.write().transactions.pop().unwrap();
		assert!(pool_state.read().transactions.is_empty());
		let tx = Extrinsic::decode(&mut &*tx).unwrap();
		assert_eq!(tx.signature, None);
		assert_eq!(tx.call, Call::submit_price_unsigned(1, 15523));
	});
}


#[test]
fn parse_price_works() {
	let test_data = vec![
		("{\"USD\":6536.92}", Some(653692)),
		("{\"USD\":65.92}", Some(6592)),
		("{\"USD\":6536.924565}", Some(653692)),
		("{\"USD\":6536}", Some(653600)),
		("{\"USD2\":6536}", None),
		("{\"USD\":\"6432\"}", None),
	];

	for (json, expected) in test_data {
		assert_eq!(expected, Example::parse_price(json));
	}
}

// Call contract in test.
	Contracts::call(
		Origin::signed(alice),
		contract_id,
		0,
		GAS_LIMIT,
		vec![],
	).unwrap();