# Alliance Pallet

The Alliance Pallet provides a collective that curates a blacklist of accounts and URLs,
presumably agreed by the voting members to be bad actors. The alliance

- provides a set of ethics against bad behavior, and
- provides recognition and influence for those teams that contribute something back to the
  ecosystem.

## Overview

The network initializes the Alliance via a Root call. After that, anyone with an approved
identity and website can apply to become a Candidate. Members will initiate a motion to
determine whether a Candidate can join the Alliance or not. The motion requires the approval of
the `MembershipManager` origin. The Alliance can also maintain a blacklist of accounts and
websites. Members can also vote to update the Alliance's rule and make announcements.

### Terminology

- Rule: The IPFS CID (hash) of the Alliance rules for the community to read and the Alliance
  members to enforce. Similar to a Code of Conduct.
- Announcement: An IPFS CID of some content that the Alliance want to announce.
- Member: An account that is already in the group of the Alliance, including three types:
  Founder, Fellow, or Ally. A member can also be kicked by the `MembershipManager` origin or
  retire by itself.
- Founder: An account who is initiated by Root with normal voting rights for basic motions and
  special veto rights for rule change and ally elevation motions.
- Fellow: An account who is elevated from Ally by Founders and other Fellows.
- Ally: An account who is approved by Founders and Fellows from Candidate. An Ally doesn't have
  voting rights.
- Candidate: An account who is trying to become a member. The applicant should already have an
  approved identity with website. The application should be submitted by the account itself with
  some deposit, or be nominated by an existing Founder or Fellow for free.
- Blacklist: A list of bad websites and addresses, items can be added or removed by Founders
  and Fellows.

## Interface

### Dispatchable Functions

#### For General Users

- `submit_candidacy` - Submit the application to become a candidate with deposit.

#### For Members (All)

- `retire` - Retire from the Alliance and release the caller's deposit.

#### For Members (Founders/Fellows)

- `propose` - Propose a motion.
- `vote` - Vote on a motion.
- `close` - Close a motion with enough votes or that has expired.
- `set_rule` - Initialize or update the Alliance's rule by IPFS CID.
- `announce` - Make announcement by IPFS CID.
- `nominate_candidate` - Nominate a non-member to become a Candidate for free.
- `approve_candidate` - Approve a candidate to become an Ally.
- `reject_candidate` - Reject a candidate and slash its deposit.
- `elevate_ally` - Approve an ally to become a Fellow.
- `kick_member` - Kick a member and slash its deposit.
- `add_blacklist_items` - Add some items, either accounts or websites, to the blacklist.
- `remove_blacklist_items` - Remove some items from the blacklist.

#### For Members (Only Founders)

- `veto` - Veto on a motion about `set_rule` and `elevate_ally`.

#### Root Calls

- `init_founders` - Initialize the founding members.
