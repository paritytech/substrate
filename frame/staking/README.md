# Staking Module

The Staking module is used to manage funds at stake by network maintainers.

- [`staking::Config`](https://docs.rs/pallet-staking/latest/pallet_staking/trait.Config.html)
- [`Call`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.Call.html)
- [`Module`](https://docs.rs/pallet-staking/latest/pallet_staking/struct.Module.html)

## Overview

The Staking module is the means by which a set of network maintainers (known as _authorities_ in
some contexts and _validators_ in others) are chosen based upon those who voluntarily place
funds under deposit. Under deposit, those funds are rewarded under normal operation but are held
at pain of _slash_ (expropriation) should the staked maintainer be found not to be discharging
its duties properly.

### Terminology
<!-- Original author of paragraph: @gavofyork -->

- Staking: The process of locking up funds for some time, placing them at risk of slashing
  (loss) in order to become a rewarded maintainer of the network.
- Validating: The process of running a node to actively maintain the network, either by
  producing blocks or guaranteeing finality of the chain.
- Nominating: The process of placing staked funds behind one or more validators in order to
  share in any reward, and punishment, they take.
- Stash account: The account holding an owner's funds used for staking.
- Controller account: The account that controls an owner's funds for staking.
- Era: A (whole) number of sessions, which is the period that the validator set (and each
  validator's active nominator set) is recalculated and where rewards are paid out.
- Slash: The punishment of a staker by reducing its funds.

### Goals
<!-- Original author of paragraph: @gavofyork -->

The staking system in Substrate NPoS is designed to make the following possible:

- Stake funds that are controlled by a cold wallet.
- Withdraw some, or deposit more, funds without interrupting the role of an entity.
- Switch between roles (nominator, validator, idle) with minimal overhead.

### Scenarios

#### Staking

Almost any interaction with the Staking module requires a process of _**bonding**_ (also known
as being a _staker_). To become *bonded*, a fund-holding account known as the _stash account_,
which holds some or all of the funds that become frozen in place as part of the staking process,
is paired with an active **controller** account, which issues instructions on how they shall be
used.

An account pair can become bonded using the [`bond`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.Call.html#variant.bond) call.

Stash accounts can update their associated controller back to their stash account using the
[`set_controller`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.Call.html#variant.set_controller)
call. 

Note: Controller accounts are being deprecated in favor of proxy accounts, so it is no longer
possible to set a unique address for a stash's controller.

There are three possible roles that any staked account pair can be in: `Validator`, `Nominator`
and `Idle` (defined in [`StakerStatus`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.StakerStatus.html)). There are three
corresponding instructions to change between roles, namely:
[`validate`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.Call.html#variant.validate),
[`nominate`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.Call.html#variant.nominate), and [`chill`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.Call.html#variant.chill).

#### Validating

A **validator** takes the role of either validating blocks or ensuring their finality,
maintaining the veracity of the network. A validator should avoid both any sort of malicious
misbehavior and going offline. Bonded accounts that state interest in being a validator do NOT
get immediately chosen as a validator. Instead, they are declared as a _candidate_ and they
_might_ get elected at the _next era_ as a validator. The result of the election is determined
by nominators and their votes.

An account can become a validator candidate via the
[`validate`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.Call.html#variant.validate) call.

#### Nomination

A **nominator** does not take any _direct_ role in maintaining the network, instead, it votes on
a set of validators  to be elected. Once interest in nomination is stated by an account, it
takes effect at the next election round. The funds in the nominator's stash account indicate the
_weight_ of its vote. Both the rewards and any punishment that a validator earns are shared
between the validator and its nominators. This rule incentivizes the nominators to NOT vote for
the misbehaving/offline validators as much as possible, simply because the nominators will also
lose funds if they vote poorly.

An account can become a nominator via the [`nominate`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.Call.html#variant.nominate) call.

#### Rewards and Slash

The **reward and slashing** procedure is the core of the Staking module, attempting to _embrace
valid behavior_ while _punishing any misbehavior or lack of availability_.

Rewards must be claimed for each era before it gets too old by `$HISTORY_DEPTH` using the
`payout_stakers` call. Any account can call `payout_stakers`, which pays the reward to the
validator as well as its nominators. Only the [`Config::MaxNominatorRewardedPerValidator`]
biggest stakers can claim their reward. This is to limit the i/o cost to mutate storage for each
nominator's account.

Slashing can occur at any point in time, once misbehavior is reported. Once slashing is
determined, a value is deducted from the balance of the validator and all the nominators who
voted for this validator (values are deducted from the _stash_ account of the slashed entity).

Slashing logic is further described in the documentation of the `slashing` module.

Similar to slashing, rewards are also shared among a validator and its associated nominators.
Yet, the reward funds are not always transferred to the stash account and can be configured. See
[Reward Calculation](https://docs.rs/pallet-staking/latest/pallet_staking/#reward-calculation) for more details.

#### Chilling

Finally, any of the roles above can choose to step back temporarily and just chill for a while.
This means that if they are a nominator, they will not be considered as voters anymore and if
they are validators, they will no longer be a candidate for the next election.

An account can step back via the [`chill`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.Call.html#variant.chill) call.

### Session managing

The module implement the trait `SessionManager`. Which is the only API to query new validator
set and allowing these validator set to be rewarded once their era is ended.

## Interface

### Dispatchable Functions

The dispatchable functions of the Staking module enable the steps needed for entities to accept
and change their role, alongside some helper functions to get/set the metadata of the module.

### Public Functions

The Staking module contains many public storage items and (im)mutable functions.

## Usage

### Example: Rewarding a validator by id.

```rust
use pallet_staking::{self as staking};

#[frame_support::pallet]
pub mod pallet {
    use super::*;
    use frame_support::pallet_prelude::*;
    use frame_system::pallet_prelude::*;

    #[pallet::pallet]
    pub struct Pallet<T>(_);

    #[pallet::config]
    pub trait Config: frame_system::Config + staking::Config {}

    #[pallet::call]
    impl<T: Config> Pallet<T> {
        /// Reward a validator.
        #[pallet::weight(0)]
        pub fn reward_myself(origin: OriginFor<T>) -> DispatchResult {
            let reported = ensure_signed(origin)?;
            <staking::Pallet<T>>::reward_by_ids(vec![(reported, 10)]);
            Ok(())
        }
    }
}
```

## Implementation Details

### Era payout

The era payout is computed using yearly inflation curve defined at
[`T::RewardCurve`](https://docs.rs/pallet-staking/latest/pallet_staking/trait.Config.html#associatedtype.RewardCurve) as such:

```nocompile
staker_payout = yearly_inflation(npos_token_staked / total_tokens) * total_tokens / era_per_year
```
This payout is used to reward stakers as defined in next section

```nocompile
remaining_payout = max_yearly_inflation * total_tokens / era_per_year - staker_payout
```
The remaining reward is send to the configurable end-point
[`T::RewardRemainder`](https://docs.rs/pallet-staking/latest/pallet_staking/trait.Config.html#associatedtype.RewardRemainder).

### Reward Calculation

Validators and nominators are rewarded at the end of each era. The total reward of an era is
calculated using the era duration and the staking rate (the total amount of tokens staked by
nominators and validators, divided by the total token supply). It aims to incentivize toward a
defined staking rate. The full specification can be found
[here](https://research.web3.foundation/en/latest/polkadot/economics/1-token-economics.html#inflation-model).

Total reward is split among validators and their nominators depending on the number of points
they received during the era. Points are added to a validator using
[`reward_by_ids`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.Call.html#variant.reward_by_ids) or
[`reward_by_indices`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.Call.html#variant.reward_by_indices).

[`Module`](https://docs.rs/pallet-staking/latest/pallet_staking/struct.Module.html) implements
[`pallet_authorship::EventHandler`](https://docs.rs/pallet-authorship/latest/pallet_authorship/trait.EventHandler.html) to add reward
points to block producer and block producer of referenced uncles.

The validator and its nominator split their reward as following:

The validator can declare an amount, named
[`commission`](https://docs.rs/pallet-staking/latest/pallet_staking/struct.ValidatorPrefs.html#structfield.commission), that does not get shared
with the nominators at each reward payout through its
[`ValidatorPrefs`](https://docs.rs/pallet-staking/latest/pallet_staking/struct.ValidatorPrefs.html). This value gets deducted from the total reward
that is paid to the validator and its nominators. The remaining portion is split among the
validator and all of the nominators that nominated the validator, proportional to the value
staked behind this validator (_i.e._ dividing the
[`own`](https://docs.rs/pallet-staking/latest/pallet_staking/struct.Exposure.html#structfield.own) or
[`others`](https://docs.rs/pallet-staking/latest/pallet_staking/struct.Exposure.html#structfield.others) by
[`total`](https://docs.rs/pallet-staking/latest/pallet_staking/struct.Exposure.html#structfield.total) in [`Exposure`](https://docs.rs/pallet-staking/latest/pallet_staking/struct.Exposure.html)).

All entities who receive a reward have the option to choose their reward destination through the
[`Payee`](https://docs.rs/pallet-staking/latest/pallet_staking/struct.Payee.html) storage item (see
[`set_payee`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.Call.html#variant.set_payee)), to be one of the following:

- Controller account, (obviously) not increasing the staked value.
- Stash account, not increasing the staked value.
- Stash account, also increasing the staked value.

### Additional Fund Management Operations

Any funds already placed into stash can be the target of the following operations:

The controller account can free a portion (or all) of the funds using the
[`unbond`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.Call.html#variant.unbond) call. Note that the funds are not immediately
accessible. Instead, a duration denoted by [`BondingDuration`](https://docs.rs/pallet-staking/latest/pallet_staking/trait.Config.html#associatedtype.BondingDuration)
(in number of eras) must pass until the funds can actually be removed. Once the
`BondingDuration` is over, the [`withdraw_unbonded`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.Call.html#variant.withdraw_unbonded)
call can be used to actually withdraw the funds.

Note that there is a limitation to the number of fund-chunks that can be scheduled to be
unlocked in the future via [`unbond`](https://docs.rs/pallet-staking/latest/pallet_staking/enum.Call.html#variant.unbond). In case this maximum
(`MAX_UNLOCKING_CHUNKS`) is reached, the bonded account _must_ first wait until a successful
call to `withdraw_unbonded` to remove some of the chunks.

### Election Algorithm

The current election algorithm is implemented based on Phragmén. The reference implementation
can be found [here](https://github.com/w3f/consensus/tree/master/NPoS).

The election algorithm, aside from electing the validators with the most stake value and votes,
tries to divide the nominator votes among candidates in an equal manner. To further assure this,
an optional post-processing can be applied that iteratively normalizes the nominator staked
values until the total difference among votes of a particular nominator are less than a
threshold.

## GenesisConfig

The Staking module depends on the [`GenesisConfig`](https://docs.rs/pallet-staking/latest/pallet_staking/struct.GenesisConfig.html). The
`GenesisConfig` is optional and allow to set some initial stakers.

## Related Modules

- [Balances](https://docs.rs/pallet-balances/latest/pallet_balances/): Used to manage values at stake.
- [Session](https://docs.rs/pallet-session/latest/pallet_session/): Used to manage sessions. Also, a list of new
  validators is stored in the Session module's `Validators` at the end of each era.

License: Apache-2.0
