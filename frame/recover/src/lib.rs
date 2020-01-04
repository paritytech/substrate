// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

/// Configuration trait.
pub trait Trait: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// The overarching call type.
	type Call: Parameter + Dispatchable<Origin=Self::Origin> + GetDispatchInfo;

	/// The currency mechanism.
	type Currency: ReservableCurrency<Self::AccountId>;

	/// The base amount of currency needed to reserve for creating a recovery setup.
	///
	/// This is held for an additional storage item whose value size is
	/// TODO bytes.
	type SetupDepositBase: Get<BalanceOf<Self>>;

	/// The amount of currency needed per additional user when creating a recovery setup.
	///
	/// This is held for adding TODO bytes more into a pre-existing storage value.
	type SetupDepositFactor: Get<BalanceOf<Self>>;

	/// The maximum amount of friends allowed in a recovery setup.
	type MaxFriends: Get<u16>;

	/// The base amount of currency needed to reserve for starting a recovery.
	///
	/// This is held for an additional storage item whose value size is
	/// TODO bytes.
	type RecoveryDeposit: Get<BalanceOf<Self>>;
}

#[derive(Clone, Eq, PartialEq, Encode, Decode, Default, RuntimeDebug)]
pub enum RecoveryStep {
	Active,
	Succeeded,
	Failed,
}

/// An open multisig operation.
#[derive(Clone, Eq, PartialEq, Encode, Decode, Default, RuntimeDebug)]
pub struct RecoveryStatus<BlockNumber, Balance, AccountId> {
	/// Denotes if the recovery process is active.
	step: RecoveryStep,
	/// The last block when someone has tried to recover the account
	last: BlockNumber,
	/// The amount held in reserve of the `depositor`, to be returned once this setup is closed.
	deposit: Balance,
	/// The approvals achieved so far, including the depositor. Always sorted.
	friends: Vec<AccountId>,
}

/// An open multisig operation.
#[derive(Clone, Eq, PartialEq, Encode, Decode, Default, RuntimeDebug)]
pub struct RecoverySetup<BlockNumber, Balance, AccountId> {
	/// The minimum amount of time between friend approvals.
	delay_period: BlockNumber
	/// The amount held in reserve of the `depositor`, to be returned once this setup is closed.
	deposit: Balance,
	/// The list of friends which can help recover an account. Always sorted.
	friends: Vec<AccountId>,
	/// The number of approving friends needed to recover an account.
	threshold: u16,
}

decl_storage! {
	trait Store for Module<T: Trait> as Utility {
		/// The set of recovery setups.
		pub RecoverySetups get(fn recovery_setup):
			map T::AccountId => Option<RecoverySetup<T::BlockNumber, BalanceOf<T>, T::AccountId>>;
		/// Active recovery attempts.
		///
		/// First account is the account to be recovered, and the second account is the user trying to
		/// recover the account.
		pub ActiveRecoveries get(fn active_recovery):
			double_map hasher(twox_64_concat) T::AccountId, twox_64_concat(T::AccountId) =>
			Option<RecoveryStatus<T::BlockNumber, BalanceOf<T>, T::AccountId>>;
		/// The final list of recovered accounts.
		///
		/// Map from the recovered account to the user who can access it.
		pub Recovered get(fn recovered_account): T::AccountId => Option<T::AccountId>;
	}
}

decl_event! {
	/// Events type.
	pub enum Event<T> where
		AccountId = <T as system::Trait>::AccountId,
	{
		/// A recovery process has been set up for an account
		RecoveryCreated(AccountId),
		/// A recovery process has been initiated by account_1 for account_2
		RecoveryInitiated(AccountId, AccountId),
		/// A recovery process by account_1 for account_2 has been vouched for by account_3
		RecoveryVouched(AccountId, AccountId, AccountId),
		/// Account_1 has recovered account_2
		AccountRecovered(AccountId, AccountId),
		/// A recovery process has been removed for an account
		RecoveryRemoved(AccountId),
	}
}

decl_error! {
	pub enum Error {
		/// User is not allowed to make a call on behalf of this account
		NotAllowed,
		/// Threshold must be greater than zero
		ZeroThreshold,
		/// Friends list must be greater than zero
		ZeroFriends,
		/// Friends list must be less than max friends
		MaxFriends,
		/// Friends list must be sorted
		NotSorted,
		/// This account is not set up for recovery
		NotSetup,
		/// This account is already set up for recovery
		AlreadySetup,
		/// A recovery process has already started for this account
		AlreadyStarted,
		/// A recovery process has not started for this rescuer
		NotStarted,
		/// This account is not a friend who can vouch
		NotFriend,
		/// The friend must wait until the delay period to vouch for this recovery
		DelayPeriod,
		/// This user has already vouched for this recovery
		AlreadyVouched,
		/// The threshold for recovering this account has not been met
		Threshold,
		/// There are still active recovery attempts that need to be closed
		StillActive,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Deposit one of this module's events by using the default implementation.
		fn deposit_event() = default;

		/// Send a call through a recovered account.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// # <weight>
		/// - The weight of the `call`.
		/// # </weight>
		#[weight = <Passthrough<<T as Trait>::Call>>::new()]
		fn as_recovered(origin, account: AccountId, call: Box<<T as Trait>::Call>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			// Check `who` is allowed to make a call on behalf of `account`
			ensure!(Self::recovered_account(&account) == Some(who), Error::<T>::NotAllowed);
			call.dispatch(frame_system::RawOrigin::Signed(account).into())
		}
		
		/// Allow Sudo to bypass the recovery process and set an alias account.
		fn set_recovered_account(origin, rescuee: AccountId, rescuer: AccountId) {
			ensure_root(origin)?;

			// Create the recovery storage item.
			<Recovered<T>>::insert(rescuee, rescuer);

			Self::deposit_event(RawEvent::AccountRecovered(rescuer, rescuee));
		}

		/// Create a recovery process for your account.
		fn create_recovery(origin, friends: Vec<T::AccountId>, threshold: u16, delay_period: T::BlockNumber) {
			let who = ensure_signed(origin)?;
			// Check account is not already set up for recovery
			ensure!(<RecoverySetups<T>>::exists(&account), Error::<T>::AlreadySetup);
			// Check user input is valid
			ensure!(threshold >= 1, Error::<T>::ZeroThreshold);
			ensure!(!friends.is_empty(), Error::<T>::ZeroFriends);
			ensure!(friends.len() < max_sigs, Error::<T>::MaxFriends);
			ensure!(Self::is_sorted(friends), Error::<T>::NotSorted);

			// Total deposit is base fee + number of friends * factor fee
			let total_deposit = T::SetupDepositBase::get() + T::SetupDepositFactor::get() * friends.len();
			// Reserve the deposit
			T::Currency::reserve(&who, total_deposit)?;

			// Create the recovery setup
			let recovery_setup = RecoverySetup {
				delay_period
				deposit: total_deposit,
				friends,
				threshold,
			};

			<RecoverySetups<T>>::insert(who, recovery_setup);

			Self::deposit_event(RawEvent::RecoveryCreated(who));
		}

		fn initiate_recovery(origin, account: AccountId) {
			let who = ensure_signed(origin)?;
			// Check that the account has a recovery setup
			ensure!(<RecoverySetups<T>>::exists(&account), Error::<T>::NotSetup);
			// Check that the recovery process has not already been started
			ensure!(!<ActiveRecoveries<T>>::exists(&account, &who), Error::<T>::AlreadyStarted);
			// Take recovery deposit
			let recovery_deposit = T::RecoveryDeposit::get();
			T::Currency::reserve(&who, recovery_deposit)?;
			// Create an active recovery status
			let recovery_status = RecoveryStatus {
				step: RecoveryStep::Active,
				last: T::BlockNumber::zero(),
				deposit: recovery_deposit,
				friends: vec![],
			};

			<ActiveRecoveries<T>>::insert(&account, &who, recovery_status);

			Self::deposit_event(RawEvent::RecoveryInitiated(who, account));
		}

		fn vouch_recovery(origin, rescuee: AccountId, rescuer: AccountId) {
			let who = ensure_signed(origin)?;

			// Check that there is a recovery setup for this rescuee
			if let Some(recovery_setup) = Self::recovery_setup(&rescuee) {
				// Check that the recovery process has been initiated for this rescuer
				if let Some(mut active_recovery) = Self::active_recovery(&rescuee, &rescuer) {
					// Make sure the voter is a friend
					ensure!(Self::is_friend(recovery_setup.friends, &who), Error::<T>::NotFriend);
					// Make sure the delay period has passed
					let current_block_number = <system::Module<T>>::block_number();
					ensure!(
						active_recovery.last + recovery_setup.delay_period >= current_block_number),
						Error::<T>::DelayPeriod
					);
					// Either insert the vouch, or return an error that the user already vouched.
					match active_recovery.friends.binary_search(&who) {
						Ok(pos) => Err(Error<T>::AlreadyVouched)?,
						Err(pos) => active_recovery.friends.insert(pos, who),
					}
					// Update the last vote time
					active_recovery.last = current_block_number;
					// Update storage with the latest details
					<ActiveRecoveries<T>>::insert(&rescuee, &rescuer, active_recovery);

					Self::deposit_event(RawEvent::RecoveryVouched(rescuer, rescuee, who));
				} else {
					Err(Error::<T>::NotStarted)?
				}
			} else {
				Err(Error::<T>::NotSetup)?
			}
		}

		/// Allow a rescuer to claim their recovered account.
		fn claim_recovery(origin, account: T::AccountId) {
			let who = ensure_signed(origin)?;
			// Check that there is a recovery setup for this rescuee
			if let Some(recovery_setup) = Self::recovery_setup(&rescuee) {
				// Check that the recovery process has been initiated for this rescuer
				if let Some(active_recovery) = Self::active_recovery(&rescuee, &rescuer) {
					// Make sure the threshold is met
					ensure!(
						recovery_setup.threshold <= active_recovery.friends.len(),
						Error::<T>::Threshold
					);

					// Create the recovery storage item
					<Recovered<T>>::insert(&account, &who)

					Self::deposit_event(RawEvent::AccountRecovered(who, rescuee));
				} else {
					Err(Error::<T>::NotStarted)?
				}
			} else {
				Err(Error::<T>::NotSetup)?
			}
		}

		/// Close an active recovery process.
		///
		/// Can only be called by the account trying to be recovered.
		fn close_recovery(origin, rescuer) {
			let who = ensure_signed(origin)?;
			if let Some(active_recovery) = <ActiveRecoveries<T>>::take(&who, &rescuer) {
				// Move the reserved funds from the rescuer to the rescuee account.
				// Acts like a slashing mechanism for those who try to maliciously recover accounts.
				T::Currency::repatriate_reserved(&rescuer, &who, active_recovery.deposit);
			} else {
				Err(Error::<T>::NotStarted)?
			}
		}

		/// Remove the recovery process for your account.
		///
		/// The user must make sure to call `close_recovery` on all active recovery attempts
		/// before calling this function.
		fn remove_recovery(origin) {
			let who = ensure_signed(origin)?;
			// Check there are no active recoveries
			let active_recoveries = <ActiveRecoveries<T>>::iter_prefix(&who);
			ensure!(active_recoveries.next().is_none(), Error::<T>::StillActive);
			// Check account has recovery setup
			if let Some(recovery_setup) = <RecoverySetups<T>>::take(&account) {
				T::Currency::unreserve(&who, recovery_setup.deposit);

				Self::deposit_event(RawEvent::RecoveryRemoved);
			}
		}
	}
}

impl<T: Trait> Module<T> {

	/// Check that friends list is sorted.
	fn is_sorted(friends: Vec<T::AccountId>) -> bool {
		friends.windows(2).all(|w| w[0] <= w[1])
	}

	fn is_friend(friends: Vec<T::AccountId>, friend: T::AccountId) -> bool {
		friends.binary_search(&friend).is_ok()
	}
}