#![cfg_attr(not(feature = "std"), no_std)]
use codec::FullCodec;
use frame_support::pallet_prelude::*;
use mangata_types::{
	multipurpose_liquidity::{ActivateKind, BondKind},
	Balance, TokenId,
};
use sp_core::U256;
use sp_runtime::{
	traits::{AtLeast32BitUnsigned, MaybeDisplay},
	Permill,
};
use sp_std::{fmt::Debug, vec::Vec};

pub trait GetMaintenanceStatusTrait {
	fn is_maintenance() -> bool;

	fn is_upgradable() -> bool;
}

pub trait StakingReservesProviderTrait {
	type AccountId: Parameter
		+ Member
		+ MaybeSerializeDeserialize
		+ Debug
		+ MaybeDisplay
		+ Ord
		+ MaxEncodedLen;

	fn can_bond(
		token_id: TokenId,
		account_id: &Self::AccountId,
		amount: Balance,
		use_balance_from: Option<BondKind>,
	) -> bool;

	fn bond(
		token_id: TokenId,
		account_id: &Self::AccountId,
		amount: Balance,
		use_balance_from: Option<BondKind>,
	) -> DispatchResult;

	fn unbond(token_id: TokenId, account_id: &Self::AccountId, amount: Balance) -> Balance;
}

pub trait ActivationReservesProviderTrait {
	type AccountId: Parameter
		+ Member
		+ MaybeSerializeDeserialize
		+ Debug
		+ MaybeDisplay
		+ Ord
		+ MaxEncodedLen;

	fn get_max_instant_unreserve_amount(token_id: TokenId, account_id: &Self::AccountId)
		-> Balance;

	fn can_activate(
		token_id: TokenId,
		account_id: &Self::AccountId,
		amount: Balance,
		use_balance_from: Option<ActivateKind>,
	) -> bool;

	fn activate(
		token_id: TokenId,
		account_id: &Self::AccountId,
		amount: Balance,
		use_balance_from: Option<ActivateKind>,
	) -> DispatchResult;

	fn deactivate(token_id: TokenId, account_id: &Self::AccountId, amount: Balance) -> Balance;
}

pub trait XykFunctionsTrait<AccountId> {
	type Balance: AtLeast32BitUnsigned
		+ FullCodec
		+ Copy
		+ MaybeSerializeDeserialize
		+ Debug
		+ Default
		+ From<Balance>
		+ Into<Balance>;

	type CurrencyId: Parameter
		+ Member
		+ Copy
		+ MaybeSerializeDeserialize
		+ Ord
		+ Default
		+ AtLeast32BitUnsigned
		+ FullCodec
		+ From<TokenId>
		+ Into<TokenId>;

	fn create_pool(
		sender: AccountId,
		first_asset_id: Self::CurrencyId,
		first_asset_amount: Self::Balance,
		second_asset_id: Self::CurrencyId,
		second_asset_amount: Self::Balance,
	) -> DispatchResult;

	fn sell_asset(
		sender: AccountId,
		sold_asset_id: Self::CurrencyId,
		bought_asset_id: Self::CurrencyId,
		sold_asset_amount: Self::Balance,
		min_amount_out: Self::Balance,
		err_upon_bad_slippage: bool,
	) -> Result<Self::Balance, DispatchError>;

	fn multiswap_sell_asset(
		sender: AccountId,
		swap_token_list: Vec<Self::CurrencyId>,
		sold_asset_amount: Self::Balance,
		min_amount_out: Self::Balance,
		err_upon_bad_slippage: bool,
		err_upon_non_slippage_fail: bool,
	) -> Result<Self::Balance, DispatchError>;

	fn do_multiswap_sell_asset(
		sender: AccountId,
		swap_token_list: Vec<Self::CurrencyId>,
		sold_asset_amount: Self::Balance,
		min_amount_out: Self::Balance,
	) -> Result<Self::Balance, DispatchError>;
	fn do_multiswap_buy_asset(
		sender: AccountId,
		swap_token_list: Vec<Self::CurrencyId>,
		bought_asset_amount: Self::Balance,
		max_amount_in: Self::Balance,
	) -> Result<Self::Balance, DispatchError>;

	fn buy_asset(
		sender: AccountId,
		sold_asset_id: Self::CurrencyId,
		bought_asset_id: Self::CurrencyId,
		bought_asset_amount: Self::Balance,
		max_amount_in: Self::Balance,
		err_upon_bad_slippage: bool,
	) -> Result<Self::Balance, DispatchError>;

	fn multiswap_buy_asset(
		sender: AccountId,
		swap_token_list: Vec<Self::CurrencyId>,
		bought_asset_amount: Self::Balance,
		max_amount_in: Self::Balance,
		err_upon_bad_slippage: bool,
		err_upon_non_slippage_fail: bool,
	) -> Result<Self::Balance, DispatchError>;

	fn mint_liquidity(
		sender: AccountId,
		first_asset_id: Self::CurrencyId,
		second_asset_id: Self::CurrencyId,
		first_asset_amount: Self::Balance,
		expected_second_asset_amount: Self::Balance,
		activate_minted_liquidity: bool,
	) -> Result<(Self::CurrencyId, Self::Balance), DispatchError>;

	fn provide_liquidity_with_conversion(
		sender: AccountId,
		first_asset_id: Self::CurrencyId,
		second_asset_id: Self::CurrencyId,
		provided_asset_id: Self::CurrencyId,
		provided_asset_amount: Self::Balance,
		activate_minted_liquidity: bool,
	) -> Result<(Self::CurrencyId, Self::Balance), DispatchError>;

	fn burn_liquidity(
		sender: AccountId,
		first_asset_id: Self::CurrencyId,
		second_asset_id: Self::CurrencyId,
		liquidity_asset_amount: Self::Balance,
	) -> DispatchResult;

	fn get_tokens_required_for_minting(
		liquidity_asset_id: Self::CurrencyId,
		liquidity_token_amount: Self::Balance,
	) -> Result<(Self::CurrencyId, Self::Balance, Self::CurrencyId, Self::Balance), DispatchError>;

	fn do_compound_rewards(
		sender: AccountId,
		liquidity_asset_id: Self::CurrencyId,
		amount_permille: Permill,
	) -> DispatchResult;

	fn is_liquidity_token(liquidity_asset_id: TokenId) -> bool;
}

pub trait ProofOfStakeRewardsApi<AccountId> {
	type Balance: AtLeast32BitUnsigned
		+ FullCodec
		+ Copy
		+ MaybeSerializeDeserialize
		+ Debug
		+ Default
		+ From<Balance>
		+ Into<Balance>;

	type CurrencyId: Parameter
		+ Member
		+ Copy
		+ MaybeSerializeDeserialize
		+ Ord
		+ Default
		+ AtLeast32BitUnsigned
		+ FullCodec
		+ From<TokenId>
		+ Into<TokenId>;

	fn enable(liquidity_token_id: Self::CurrencyId, weight: u8);

	fn disable(liquidity_token_id: Self::CurrencyId);

	fn is_enabled(
		liquidity_token_id: Self::CurrencyId,
	) -> bool;

	fn claim_rewards_all(
		sender: AccountId,
		liquidity_token_id: Self::CurrencyId,
	) -> Result<Self::Balance, DispatchError>;

	// Activation & deactivation should happen in PoS
	fn activate_liquidity(
		sender: AccountId,
		liquidity_token_id: Self::CurrencyId,
		amount: Self::Balance,
		use_balance_from: Option<ActivateKind>,
	) -> DispatchResult;

	// Activation & deactivation should happen in PoS
	fn deactivate_liquidity(
		sender: AccountId,
		liquidity_token_id: Self::CurrencyId,
		amount: Self::Balance,
	) -> DispatchResult;

	fn calculate_rewards_amount(
		user: AccountId,
		liquidity_asset_id: Self::CurrencyId,
	) -> Result<Balance, DispatchError>;
}

pub trait PreValidateSwaps {
	type AccountId: Parameter
		+ Member
		+ MaybeSerializeDeserialize
		+ Debug
		+ MaybeDisplay
		+ Ord
		+ MaxEncodedLen;

	type Balance: AtLeast32BitUnsigned
		+ FullCodec
		+ Copy
		+ MaybeSerializeDeserialize
		+ Debug
		+ Default
		+ From<Balance>
		+ Into<Balance>;

	type CurrencyId: Parameter
		+ Member
		+ Copy
		+ MaybeSerializeDeserialize
		+ Ord
		+ Default
		+ AtLeast32BitUnsigned
		+ FullCodec
		+ From<TokenId>
		+ Into<TokenId>;

	fn pre_validate_sell_asset(
		sender: &Self::AccountId,
		sold_asset_id: Self::CurrencyId,
		bought_asset_id: Self::CurrencyId,
		sold_asset_amount: Self::Balance,
		min_amount_out: Self::Balance,
	) -> Result<
		(Self::Balance, Self::Balance, Self::Balance, Self::Balance, Self::Balance, Self::Balance),
		DispatchError,
	>;

	fn pre_validate_multiswap_sell_asset(
		sender: &Self::AccountId,
		swap_token_list: Vec<Self::CurrencyId>,
		sold_asset_amount: Self::Balance,
		min_amount_out: Self::Balance,
	) -> Result<
		(
			Self::Balance,
			Self::Balance,
			Self::Balance,
			Self::Balance,
			Self::Balance,
			Self::CurrencyId,
			Self::CurrencyId,
		),
		DispatchError,
	>;

	fn pre_validate_buy_asset(
		sender: &Self::AccountId,
		sold_asset_id: Self::CurrencyId,
		bought_asset_id: Self::CurrencyId,
		bought_asset_amount: Self::Balance,
		max_amount_in: Self::Balance,
	) -> Result<
		(Self::Balance, Self::Balance, Self::Balance, Self::Balance, Self::Balance, Self::Balance),
		DispatchError,
	>;

	fn pre_validate_multiswap_buy_asset(
		sender: &Self::AccountId,
		swap_token_list: Vec<Self::CurrencyId>,
		final_bought_asset_amount: Self::Balance,
		max_amount_in: Self::Balance,
	) -> Result<
		(
			Self::Balance,
			Self::Balance,
			Self::Balance,
			Self::Balance,
			Self::Balance,
			Self::CurrencyId,
			Self::CurrencyId,
		),
		DispatchError,
	>;
}

pub trait FeeLockTriggerTrait<AccountId> {
	fn process_fee_lock(who: &AccountId) -> DispatchResult;

	fn can_unlock_fee(who: &AccountId) -> DispatchResult;

	fn is_whitelisted(token_id: TokenId) -> bool;

	fn get_swap_valuation_for_token(
		valuating_token_id: TokenId,
		valuating_token_amount: Balance,
	) -> Option<Balance>;

	fn unlock_fee(who: &AccountId) -> DispatchResult;
}

pub trait ComputeIssuance {
	fn initialize() {}
	fn compute_issuance(n: u32);
}

pub trait GetIssuance {
	fn get_all_issuance(n: u32) -> Option<(Balance, Balance)>;
	fn get_liquidity_mining_issuance(n: u32) -> Option<Balance>;
	fn get_staking_issuance(n: u32) -> Option<Balance>;
}

pub trait Valuate {
	type Balance: AtLeast32BitUnsigned
		+ FullCodec
		+ Copy
		+ MaybeSerializeDeserialize
		+ Debug
		+ Default
		+ From<Balance>
		+ Into<Balance>;

	type CurrencyId: Parameter
		+ Member
		+ Copy
		+ MaybeSerializeDeserialize
		+ Ord
		+ Default
		+ AtLeast32BitUnsigned
		+ FullCodec
		+ From<TokenId>
		+ Into<TokenId>;

	fn get_liquidity_asset(
		first_asset_id: Self::CurrencyId,
		second_asset_id: Self::CurrencyId,
	) -> Result<TokenId, DispatchError>;

	fn get_liquidity_token_mga_pool(
		liquidity_token_id: Self::CurrencyId,
	) -> Result<(Self::CurrencyId, Self::CurrencyId), DispatchError>;

	fn valuate_liquidity_token(
		liquidity_token_id: Self::CurrencyId,
		liquidity_token_amount: Self::Balance,
	) -> Self::Balance;

	fn scale_liquidity_by_mga_valuation(
		mga_valuation: Self::Balance,
		liquidity_token_amount: Self::Balance,
		mga_token_amount: Self::Balance,
	) -> Self::Balance;

	fn get_pool_state(liquidity_token_id: Self::CurrencyId) -> Option<(Balance, Balance)>;

	fn get_reserves(
		first_asset_id: TokenId,
		second_asset_id: TokenId,
	) -> Result<(Balance, Balance), DispatchError>;
}

pub trait PoolCreateApi {
	type AccountId: Parameter
		+ Member
		+ MaybeSerializeDeserialize
		+ Debug
		+ MaybeDisplay
		+ Ord
		+ MaxEncodedLen;

	fn pool_exists(first: TokenId, second: TokenId) -> bool;

	fn pool_create(
		account: Self::AccountId,
		first: TokenId,
		first_amount: Balance,
		second: TokenId,
		second_amount: Balance,
	) -> Option<(TokenId, Balance)>;
}

pub trait LiquidityMiningApi {
	fn distribute_rewards(liquidity_mining_rewards: Balance);
}

pub trait AssetRegistryApi {
	fn enable_pool_creation(assets: (TokenId, TokenId)) -> bool;
}
