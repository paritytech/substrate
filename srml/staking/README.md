# Staking Module

<!-- Original author of paragraph: @gavofyork -->
The staking module is the means by which a set of network maintainers (known as "authorities" in some contexts and "validators" in others) are chosen based upon those who voluntarily place funds under deposit. Under deposit, those funds are rewarded under normal operation but are held at pain of "slash" (expropriation) should they be found not to bee discharhing their duties properly [[1](#references)]. 

### Overview 

### Terminology
<!-- Original author of paragraph: @gavofyork -->

- Staking: The process of locking up funds for some time, placing them at risk of slashing (loss) in order to become a rewarded maintainer of the network.
- Validating: The process of running a node to actively maintain the network, either by producing blocks or guaranteeing finality of the chain.
- Nominating: The process of placing staked funds behind one or more validators in order to share in any reward, and punishment, they take.
- Stash account: The account holding an owner's funds used for staking.
- Controller account: The account which controls am owner's funds for staking.
- Era: A (whole) number of sessions which is the period that the validator set (and each validator's active nominator set) is recalculated and where rewards are paid out.
- Slash: The punishment of a staker by reducing their funds. 

### Goals
<!-- Original author of paragraph: @gavofyork -->

The staking system in Substrate NPoS is designed to achieve three goals:
- It should be possible to stake funds that are controlled by a cold wallet.
- It should be possible to withdraw some, or deposit more, funds without interrupting  the role of t.
- It should be possible to switch between roles (nominator, validator, idle) with minimal overhead.

### Scenarios

#### Staking 

Almost any interaction with the staking module requires at least one account to become **bonded**, also known as being a **staker**. For this, all that it is needed is a secondary _**stash account**_ which will hold the staked funds. Henceforth, the former account that initiated the interest is called the **controller** and the later, holding the funds, is named the **stash**. Also, note that this implies that entering the staking process requires an _account pair_, one of which to take the role of the controller and one to be the frozen stash account (any value locked in stash cannot be used, hence called _frozen_). This process in the public API is mostly referred to as _bonding_ via the `bond()` function. 

Any account pair successfully placed at stake can accept three possible roles, namely: `validate`, `nominate` or simply `chill`. Note that during the process of accepting these roles, the _controller_ account is always responsible for declaring interest and the _stash_ account stays untouched, without directly interacting in any operation. 

#### Validating

A **validator** takes the role of either validating blocks or ensuring their finality, maintaining the veracity of the network in other words. A validator should avoid both any sort of malicious misbehavior and going offline. Bonded accounts that state interest in being a validator do NOT get immediately chosen as a validator. Instead, they are declared as a _candidate_ and they _might_ get elected at the _next **era**_ as a validator. The result of election is determined by nominators and their votes. An account can become a validator via the `validate()` call.

#### Nomination 

A **nominator** does not take any _direct_ role in maintaining the network, instead, it votes on a set of validators to be elected. Once interest in nomination is stated by an account, it takes effect _immediately_, meaning that their votes will be taken into account at the next election round. As mentioned above, a nominator must also place some fund in a stash account, essentially indicating the _weight_ of their vote. In some sense, the nominator bets on the honesty of a set of validators by voting for them, with the goal of having a share at the reward granted to them. Any rewards given to a validator is shared among that validator and all of the nominators that voted for it. The same logic applies to the slash of a validator; if a validator misbehaves all of its nominators also get slashed. This rule incentivizes the nominators to NOT vote for the misbehaving/offline validators as much as possible, simply because the nominators will also lose funds if they vote poorly. An account can become a nominator via the `nominate()` call.

#### Rewards and Slash

The **reward and slashing** procedure are the core of the staking module, attempting to _embrace valid behavior_ while _punishing any misbehavior or lack of availability_. Slashing can occur at any point in time, once a misbehavior is reported. One such misbehavior is a validator to be detected as offline more than a certain number of times. Once slashing is determined, a value is deducted from the balance of validator and all the nominators who voted for this validator. Same rules apply to the rewards in the sense of being shared among validator and its associated nominators. 

Finally, any of the roles above can choose to temporarily step back and just chill for a while. This means that if they are a nominator, they will not be considered as voters anymore and if they are validators, they will no longer be a candidate for the next election (again, both effects apply at the beginning of the next era). An account can step back via the `chill()` call.

## Public Interface

The staking module contains many public storage items and (im)mutable, and dispatchable, functions. Please refer to the [`Module`](https://crates.parity.io/srml_staking/struct.Module.html) struct definition for more details.

## Usage Example

### Bonding and Accepting Roles

An arbitrary account pair, given that the associated stash has the required funds, can become stakers via the following call:

```rust
// bond account 3 as stash
// account 4 as controller 
// with stash value 1500 units 
// while the rewards get transferred to the controller account.
Staking::bond(Origin::signed(3), 4, 1500, RewardDestination::Controller);
```

To state desire in becoming a validator: 

```rust
// controller account 4 states desire for validation with the given preferences.
Staking::validate(Origin::signed(4), ValidatorPrefs::default()); 
```

Note that, as mentioned, the stash account is transparent in such calls and only the controller initiates the function calls.

Similarly, to state desire in nominating: 

```rust
// controller account 4 nominates for account 10 and 20.
Staking::nominate(Origin::signed(4), vec![20, 10]);
```

Finally, account 4 can withdraw from any of the above roles via

```rust
Staking::chill(Origin::signed(4));
```


## Implementation Details

### Slot Stake 

The term `slot_stake` will be used throughout this section. It refers to a value calculated at the end of each era, containing the _minimum value at stake among all validators._

### Reward Calculation 

 - Rewards are recorded **per-session** and paid **per-era**. The value of reward for each session is calculated at the end of the session based on the timeliness of the session, then accumulated to be paid later. The value of the new _per-session-reward_ is calculated at the end of each era by multiplying `slot_stake` and a configuration storage named `SessionReward`. 
 - Once a new era is triggered, rewards are paid to the validators and the associated nominators. 
   - The validator can declare an amount, named `validator_payment`, that does not get shared with the nominators at each reward payout through their `ValidatorPrefs`. This value gets deducted from the total reward that can be paid. The remaining portion is split among the validator and all of the nominators who had a vote for this validator, proportional to their staked value. 
  - All entities who receive a reward have the option to choose their reward destination, through the `Payee` storage (see `set_payee()`), to be one of the following: 
    - Controller account.
    - Stash account, not increasing the staked value.
    - Stash account, also increasing the staked value.

### Slashing details 

- A validator can be _reported_ to be offline at any point via `on_offline_validator` public function. 
- Each validator declares how many times they can be _reported_ before it actually gets slashed via the `unstake_threshold` in `ValidatorPrefs`. On top of this, the module also introduces a `OfflineSlashGrace`, which applies to all validators and prevents them from getting immediately slashed.
- Similar to the reward value, the slash value is updated at the end of each era by multiplying `slot_stake` and a configuration storage item, `OfflineSlash`.
- Once a validator has been reported a sufficient amount of times, the actual value that gets deducted from that validator, and every single nominator that voted for it calculated by multiplying the result of the above point by `2.pow(unstake_threshold)`.
  - If the previous overflow, then `slot_stake` is used.
  - If the previous is more than what the validator/nominator has in stake, all of their stake is slashed (`.max(total_stake)` in other words).

### Additional Fund Management Operations

Any funds already placed into stash can be the target of the following operations:

- The controller account can free an portion (or all) of the funds using the `unbond()` call. Note that the funds are not immediately accessible, instead, a duration denoted by `BondingDuration` number of eras must pass until the funds can be actually removed.
- To actually remove the funds, once the bonding duration is over, the `withdraw_unbonded()` can be used.
- As opposed to the above, additional funds can be added to the stash account via the `bond_extra()` transaction call. 

### Election algorithm details.

Current election algorithm is implemented based on Phragmén. The reference implementation can be found [here](https://github.com/w3f/consensus/tree/master/NPoS).

## GenesisConfig

See the [`GensisConfig`](https://crates.parity.io/srml_staking/struct.GenesisConfig.html) for a list of attributed that can be provided.

## Related Modules 

- [**Balances**](https://crates.parity.io/srml_balances/index.html): Used to manage values at stake.
- [**Sessions**](https://crates.parity.io/srml_session/index.html): Used to manage sessions. Also, a list of new validators is also stored in the sessions module's `Validators` at the end of each era.
- [**System**](https://crates.parity.io/srml_system/index.html): Used to obtain block number and time, among other details.

# References

1. This document is written as a more verbose version of the original [Staking.md](./Staking.md) file. Some sections, (denoted by `[1]`) are taken directly from the aforementioned document.
