///! Traits and default implementation for paying transaction fees.
use crate::{NegativeImbalanceOf, Trait};
use codec::FullCodec;
use frame_support::{
	traits::{Currency, ExistenceRequirement, Get, Imbalance, OnUnbalanced, WithdrawReason},
	unsigned::TransactionValidityError,
};
use sp_runtime::{
	traits::{AtLeast32BitUnsigned, DispatchInfoOf, MaybeSerializeDeserialize, PostDispatchInfoOf},
	transaction_validity::InvalidTransaction,
};
use sp_std::{fmt::Debug, marker::PhantomData};

/// Handle withdrawing, refunding and depositing of transaction fees.
pub trait OnChargeTransaction<T: Trait> {
	type LiquidityInfo: Default;

	/// Before the transaction is executed the payment of the transaction fees need to be secured.
	fn withdraw_fee(
		who: &T::AccountId,
		call: &T::Call,
		dispatch_info: &DispatchInfoOf<T::Call>,
		fee: T::Balance,
		tip: T::Balance,
	) -> Result<Self::LiquidityInfo, TransactionValidityError>;

	/// After the transaction was executed and the correct fees where collected, the resulting funds can be spend here.
	fn deposit_fee(
		who: &T::AccountId,
		dispatch_info: &DispatchInfoOf<T::Call>,
		post_info: &PostDispatchInfoOf<T::Call>,
		fee: T::Balance,
		tip: T::Balance,
		liquidity_info: Self::LiquidityInfo,
	) -> Result<(), TransactionValidityError>;
}

/// Implements the transaction payment for a Currency (eg. the pallet_balances) using an unbalance handler
/// (`[OnUnbalanced]`).
pub struct CurrencyAdapter<C, OU>(PhantomData<C>, PhantomData<OU>);

/// Default implementation for a Currency and an OnUnbalanced handler.
impl<T, C, OU, B> OnChargeTransaction<T> for CurrencyAdapter<C, OU>
where
	B: AtLeast32BitUnsigned + FullCodec + Copy + MaybeSerializeDeserialize + Debug + Default + Send + Sync,
	T: Trait<Balance = B>,
	T::TransactionByteFee: Get<B>,
	C: Currency<<T as frame_system::Trait>::AccountId, Balance = B>,
	C::PositiveImbalance: Imbalance<B, Opposite = C::NegativeImbalance>,
	C::NegativeImbalance: Imbalance<B, Opposite = C::PositiveImbalance>,
	OU: OnUnbalanced<NegativeImbalanceOf<C, T>>,
{
	type LiquidityInfo = Option<NegativeImbalanceOf<C, T>>;

	/// Withdraw the predicted fee from the transaction origin.
	fn withdraw_fee(
		who: &T::AccountId,
		_call: &T::Call,
		_info: &DispatchInfoOf<T::Call>,
		fee: B,
		tip: B,
	) -> Result<Self::LiquidityInfo, TransactionValidityError> {
		if fee.is_zero() {
			return Ok(None);
		}
		match C::withdraw(
			who,
			fee,
			if tip.is_zero() {
				WithdrawReason::TransactionPayment.into()
			} else {
				WithdrawReason::TransactionPayment | WithdrawReason::Tip
			},
			ExistenceRequirement::KeepAlive,
		) {
			Ok(imbalance) => Ok(Some(imbalance)),
			Err(_) => Err(InvalidTransaction::Payment.into()),
		}
	}

	/// Hand the fee and the tip over to the `[OnUnbalanced]` implementation. Since the predicted fee might have been
	/// too high, parts of the fee may be refunded.
	fn deposit_fee(
		who: &T::AccountId,
		_dispatch_info: &DispatchInfoOf<T::Call>,
		_post_info: &PostDispatchInfoOf<T::Call>,
		fee: B,
		tip: B,
		liquidity_info: Self::LiquidityInfo,
	) -> Result<(), TransactionValidityError> {
		if let Some(paid) = liquidity_info {
			// Calculate how much refund we should return
			let refund_amount = paid.peek().saturating_sub(fee);
			// refund to the the account that paid the fees. If this fails, the account might have dropped below the
			// existential balance. In that case we don't refund anything. sorry. :(
			let refund_imbalance =
				C::deposit_into_existing(&who, refund_amount).unwrap_or_else(|_| C::PositiveImbalance::zero());
			// merge the imbalance caused by paying the fees and refunding parts of it again.
			let adjusted_paid = paid
				.offset(refund_imbalance)
				.map_err(|_| TransactionValidityError::Invalid(InvalidTransaction::Payment))?;
			// Call someone else to handle the imbalance (fee and tip separately)
			let imbalances = adjusted_paid.split(tip);
			OU::on_unbalanceds(Some(imbalances.0).into_iter().chain(Some(imbalances.1)));
		}
		Ok(())
	}
}
