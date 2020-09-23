# Recovery Pallet

- [`recovery::Trait`](https://docs.rs/pallet-recovery/latest/pallet_recovery/trait.Trait.html)
- [`Call`](https://docs.rs/pallet-recovery/latest/pallet_recovery/enum.Call.html)

## Overview

The Recovery pallet is an M-of-N social recovery tool for users to gain
access to their accounts if the private key or other authentication mechanism
is lost. Through this pallet, a user is able to make calls on-behalf-of another
account which they have recovered. The recovery process is protected by trusted
"friends" whom the original account owner chooses. A threshold (M) out of N
friends are needed to give another account access to the recoverable account.

### Recovery Configuration

The recovery process for each recoverable account can be configured by the account owner.
They are able to choose:
* `friends` - The list of friends that the account owner trusts to protect the
  recovery process for their account.
* `threshold` - The number of friends that need to approve a recovery process for
  the account to be successfully recovered.
* `delay_period` - The minimum number of blocks after the beginning of the recovery
  process that need to pass before the account can be successfully recovered.

There is a configurable deposit that all users need to pay to create a recovery
configuration. This deposit is composed of a base deposit plus a multiplier for
the number of friends chosen. This deposit is returned in full when the account
owner removes their recovery configuration.

### Recovery Life Cycle

The intended life cycle of a successful recovery takes the following steps:
1. The account owner calls `create_recovery` to set up a recovery configuration
   for their account.
2. At some later time, the account owner loses access to their account and wants
   to recover it. Likely, they will need to create a new account and fund it with
   enough balance to support the transaction fees and the deposit for the
   recovery process.
3. Using this new account, they call `initiate_recovery`.
4. Then the account owner would contact their configured friends to vouch for
   the recovery attempt. The account owner would provide their old account id
   and the new account id, and friends would call `vouch_recovery` with those
   parameters.
5. Once a threshold number of friends have vouched for the recovery attempt,
   the account owner needs to wait until the delay period has passed, starting
   when they initiated the recovery process.
6. Now the account owner is able to call `claim_recovery`, which subsequently
   allows them to call `as_recovered` and directly make calls on-behalf-of the lost
   account.
7. Using the now recovered account, the account owner can call `close_recovery`
   on the recovery process they opened, reclaiming the recovery deposit they
   placed.
8. Then the account owner should then call `remove_recovery` to remove the recovery
   configuration on the recovered account and reclaim the recovery configuration
   deposit they placed.
9. Using `as_recovered`, the account owner is able to call any other pallets
   to clean up their state and reclaim any reserved or locked funds. They
   can then transfer all funds from the recovered account to the new account.
10. When the recovered account becomes reaped (i.e. its free and reserved
    balance drops to zero), the final recovery link is removed.

### Malicious Recovery Attempts

Initializing a the recovery process for a recoverable account is open and
permissionless. However, the recovery deposit is an economic deterrent that
should disincentivize would-be attackers from trying to maliciously recover
accounts.

The recovery deposit can always be claimed by the account which is trying to
to be recovered. In the case of a malicious recovery attempt, the account
owner who still has access to their account can claim the deposit and
essentially punish the malicious user.

Furthermore, the malicious recovery attempt can only be successful if the
attacker is also able to get enough friends to vouch for the recovery attempt.
In the case where the account owner prevents a malicious recovery process,
this pallet makes it near-zero cost to re-configure the recovery settings and
remove/replace friends who are acting inappropriately.

### Safety Considerations

It is important to note that this is a powerful pallet that can compromise the
security of an account if used incorrectly. Some recommended practices for users
of this pallet are:

* Configure a significant `delay_period` for your recovery process: As long as you
  have access to your recoverable account, you need only check the blockchain once
  every `delay_period` blocks to ensure that no recovery attempt is successful
  against your account. Using off-chain notification systems can help with this,
  but ultimately, setting a large `delay_period` means that even the most skilled
  attacker will need to wait this long before they can access your account.
* Use a high threshold of approvals: Setting a value of 1 for the threshold means
  that any of your friends would be able to recover your account. They would
  simply need to start a recovery process and approve their own process. Similarly,
  a threshold of 2 would mean that any 2 friends could work together to gain
  access to your account. The only way to prevent against these kinds of attacks
  is to choose a high threshold of approvals and select from a diverse friend
  group that would not be able to reasonably coordinate with one another.
* Reset your configuration over time: Since the entire deposit of creating a
  recovery configuration is returned to the user, the only cost of updating
  your recovery configuration is the transaction fees for the calls. Thus,
  it is strongly encouraged to regularly update your recovery configuration
  as your life changes and your relationship with new and existing friends
  change as well.

## Interface

### Dispatchable Functions

#### For General Users

* `create_recovery` - Create a recovery configuration for your account and make it recoverable.
* `initiate_recovery` - Start the recovery process for a recoverable account.

#### For Friends of a Recoverable Account
* `vouch_recovery` - As a `friend` of a recoverable account, vouch for a recovery attempt on the account.

#### For a User Who Successfully Recovered an Account

* `claim_recovery` - Claim access to the account that you have successfully completed the recovery process for.
* `as_recovered` - Send a transaction as an account that you have recovered. See other functions below.

#### For the Recoverable Account

* `close_recovery` - Close an active recovery process for your account and reclaim the recovery deposit.
* `remove_recovery` - Remove the recovery configuration from the account, making it un-recoverable.

#### For Super Users

* `set_recovered` - The ROOT origin is able to skip the recovery process and directly allow
  one account to access another.

License: Apache-2.0