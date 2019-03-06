# Module Summary, Description and Specification

## Staking

The staking module is the means by which a set of network maintainers (known as "authorities" in some contexts and "validators" in others) are chosen based upon those who voluntarily place funds under deposit. Under deposit, those funds are rewarded under normal operation but are held at pain of "slash" (expropriation) should they be found not to bee discharhing their duties properly.

### Vocabulary

- Staking: The process of locking up funds for some time, placing them at risk of slashing (loss) in order to become a rewarded maintainer of the network.
- Validating: The process of running a node to actively maintain the network, either by producing blocks or guaranteeing finality of the chain.
- Nominating: The process of placing staked funds behind one or more validators in order to share in any reward, and punishment, they take.
- Stash account: The account holding an owner's funds used for staking.
- Controller account: The account which controls am owner's funds for staking.
- Era: A (whole) number of sessions which is the period that the validator set (and each validator's active nominator set) is recalculated and where rewards are paid out.
- Slash: The punishment of a staker by reducing their funds.

### Goals

The staking system in Substrate NPoS is designed to achieve three goals:
- It should be possible to stake funds that are controlled by a cold wallet.
- It should be possible to withdraw some, or deposit more, funds without interrupting  the role of t.
- It should be possible to switch between roles (nominator, validator, idle) with minimal overhead.

### Stash account

To achieve these goals, Substrate NPoS distinguishes the act of staking from the act of declaring the role (nominating or validating) desired. An owner of funds wanting to validate or nominate must first deposit some or all of an account's balance to be managed by the staking system. When they do this, we call it *staking* and we say the funds are *under management* and *bonded*. A transaction-dispatchable call `bond` is provided for this. Once an account has funds bonded, those funds may no longer be transfered out or deducted in any way, including for transaction fees payment. If all funds of the account are thus used, then the account is effectively locked since it is unable to pay for any transactions.

Since the funds under management may be entirely frozen, and quite possibly controlled only by an offline cold wallet device, another account is used to control the staking activity of these funds. At the point of staking an account, this account is declared. Whereas the account holding the funds under management is known as the *stash*, the second account that controls the staking activity is called the *controller* account. Once staked, the stash account has no further transactional interaction with the staking module; all transactions regarding the staking activity of the stash are signed with the controller account. If there are unmanaged funds, then non-staking transactions may still be issued from the stash account, such as transfering funds out with the balances module.

### Controller account

Once the stash account's funds are committed under management of the staking system, then the controller account takes over. Three operations allow the owner to control their role in the staking system, switching between idle (no role at all) with the `chill` call; switching to a validator role with the `validate` call; and finally switching to the nominator role with `nominate`. In the case of the latter, the set of validators they are happy to entrust their stake to is also provided. The effect of these operations is felt at the next point that the nominator/validator set is recalculated, which will usually be at the end of the current era.

Three further operations are provided for the fund management: two for withdrawing funds that are under management of the staking system `unbond` and `withdraw_unbonded`, and another for introducing additional funds under management, `bond_extra`. Regarding the withdrawal of funds, the funds become inactive in the staking system from the era following the `unbond` call, however they may not be transfered out of the account (by a normal transfer operation using the stash key) until the bonding period has ended. At that point, the `withdraw_unbonded` must be called before the funds are free to bee used.

Funds deposited into the stash account will not automatically be introduced under management of the staking system: They may be retransfered out of the stash account normally until they enter under management. If there is a desire to bring such funds not yet under managment into the staking system, a separate transaction calling `bond_extra` must be issued to do this.

### Validating

A `validate` transaction takes a parameter of type `ValidatorPrefs`; this encodes a set of options available to validators. There are two options here: the `unstake_threshold` and `validator_payment`. The former allows a validator to control how long they acrue punishment for being offline before they are finally removed from the validator list and have the slash deducted. There is a tradeoff between being removed from the validator set early and thus missing out on an era's rewards and risking a much more substantial punishment as the slash amount increases exponentially with each offline infraction.

The latter option, `validator_payment`, allows a validator to reserve some amount of funds for themselves before the rest is shared out, *pro rata* amongst itself and the nominators. By "default", this is zero which means the validator and nominators partake in the rewards equally. However, by raising this, the validator may reserve some of the funds for themselves, making them a less attractive financial proposal compared to other less "greedy" validators. This allows over-subscribed validators to monetise their reputation and provides a macroeconomic mechanism of redistributing nominations between different validators.

### Nonminating

A `nominate` transaction take a single parameter which is the set of validator identities the nominator approves of their stake backing. Nomination does not allow control of *how much* of the stake backs any individual validator. If a staker wishes to have such fine-grained control, they could split their funds between several accounts and stake each individually to effect such a arrangement.

At the beginning of each era, each staker's funds is automatically allocated between some or all of each of their nominated validators, possibly with some (or, in extremis all) left unallocated. Only the portion of their stake that is allocated generates rewards and is at risk of slashing.

When an era begins, a basic usage of the Phragmén method gives an initial allocation. Over some initial period (perhaps one session) in the era, third-parties may submit their own solutions (typically determined by running Phragmén more extensively) in order to further optimise the allocation between nominators and validators. At the end of the initial period, the allocation is fixed for the rest of the era. During the initial period, any slashing uses the initial, suboptimal allocations.

### Rewards & Payouts

At the end of each successful session, a reward is accrued according to the overall timeliness of blocks. If the session's aveerage block period was optimal, then the maximum reward is accrued; the fewer blocks producted, the lower the reward. At the end of each era, each validator is paid this overall reward into an account of their choosing. Nominator portions are distributed *pro rata* for the amount of stake backing that validator and according to the validator's preferences.

There are three possible payment destinations or `Payee`s and this is set during the call to `bond` and may be updated by dispatching a `set_payee` transaction. The `Controller` payee places rewards into the controller account. The `Stash` and `Staked` targets both place rewards into the stash account, but the latter also places the rewards immediately under management. 

### Slashing

Slashing happens when a validator has misbehaved in some way. Funds may be slashed up until the point they are withdrawn from management (using the `withdraw_unbonded` call). Digests of validator and nominator arrangements are recorded in order to ensure that historical misbehaviour can be properly attributed to stakes and punished.

For a slash on some validator balance and associated nominator balances, the validator balance is reduced at preference. If the slash amount is greater than that which the validator has at stake, then the nominators balances are reduced pro rata for the remainder.