# Alliance Pallet

The Alliance Pallet provides a collective that curates a list of accounts and URLs, deemed by
the voting members to be unscrupulous actors. The Alliance

- provides a set of ethics against bad behavior, and
- provides recognition and influence for those teams that contribute something back to the
  ecosystem.

## Overview

The network initializes the Alliance via a Root call. After that, anyone with an approved
identity and website can join as an Ally. The `MembershipManager` origin can elevate Allies to
Fellows, giving them voting rights within the Alliance.

Voting members of the Alliance maintain a list of accounts and websites. Members can also vote
to update the Alliance's rule and make announcements.

### Terminology

- Rule: The IPFS CID (hash) of the Alliance rules for the community to read and the Alliance
  members to enforce. Similar to a Charter or Code of Conduct.
- Announcement: An IPFS CID of some content that the Alliance want to announce.
- Member: An account that is already in the group of the Alliance, including three types:
  Fellow, or Ally. A member can also be kicked by the `MembershipManager` origin
  or retire by itself.
- Fellow: An account who is elevated from Ally by other Fellows.
- Ally: An account who would like to join the Alliance. To become a voting member (Fellow), it
  will need approval from the `MembershipManager` origin. Any account can join as an Ally either
  by placing a deposit or by nomination from a voting member.
- Unscrupulous List: A list of bad websites and addresses; items can be added or removed by
  voting members.

## Interface

### Dispatchable Functions

#### For General Users

- `join_alliance` - Join the Alliance as an Ally. This requires a slashable deposit.

#### For Members (All)

- `give_retirement_notice` - Give a retirement notice and start a retirement period required to
  pass in order to retire.
- `retire` - Retire from the Alliance and release the caller's deposit.

#### For Voting Members

- `propose` - Propose a motion.
- `vote` - Vote on a motion.
- `close` - Close a motion with enough votes or that has expired.
- `set_rule` - Initialize or update the Alliance's rule by IPFS CID.
- `announce` - Make announcement by IPFS CID.
- `nominate_ally` - Nominate a non-member to become an Ally, without deposit.
- `elevate_ally` - Approve an ally to become a Fellow.
- `kick_member` - Kick a member and slash its deposit.
- `add_unscrupulous_items` - Add some items, either accounts or websites, to the list of
  unscrupulous items.
- `remove_unscrupulous_items` - Remove some items from the list of unscrupulous items.
- `abdicate_fellow_status` - Abdicate one's voting rights, demoting themself to Ally.

#### Root Calls

- `init_members` - Initialize the Alliance, onboard fellows and allies.
- `disband` - Disband the Alliance, remove all active members and unreserve deposits.
