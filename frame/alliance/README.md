# Alliance Pallet

The Alliance Pallet provides a DAO to form an industry group that does two main things:

- provide a set of ethics against bad behaviors.
- provide recognition and influence for those teams that contribute something back to the ecosystem.

## Overview

The Alliance first needs to initialize the Founders with sudo permissions.
After that, anyone with an approved identity and website can apply to become a Candidate. 
Members will initiate a motion to determine whether a Candidate can join the Alliance or not. 
The motion requires the approval of over 2/3 majority. 
The Alliance can also maintain a blacklist list about accounts and websites. 
Members can also vote to update the alliance's rule and make announcements.

### Terminology

- Rule: The IPFS Hash of the Alliance Rule for the community to read
  and the alliance members to enforce for the management. 

- Announcement: An IPFS hash of some content that the Alliance want to announce.

- Member: An account which is already in the group of the Alliance,
  including three types: Founder, Fellow, Ally.
  Member can also be kicked by super majority motion or retire by itself. 

- Founder: An account who is initiated by sudo with normal voting rights for basic motions
  and special veto rights for rule change and ally elevation motions.

- Fellow: An account who is elevated from Ally by Founders and other Fellows from Ally.

- Ally: An account who is approved by Founders and Fellows from Candidate.
  An Ally doesn't have voting rights.

- Candidate: An account who is trying to become a member.
  The applicant should already have an approved identity with website.
  The application should be submitted by the account itself with some token as deposit,
  or be nominated by an existing Founder or Fellow for free.

- Blacklist: A list of bad websites and addresses, and can be added or removed items by Founders and Fellows.

## Interface

### Dispatchable Functions

#### For General Users
- `submit_candidacy` - Submit the application to become a candidate with deposit.

#### For Members (All)
- `retire` - Member retire to out of the Alliance and release its deposit.

#### For Members (Founders/Fellows) 

- `propose` - Propose a motion.
- `vote` - Vote on a motion. 
- `close` - Close a motion with enough votes or expired. 
- `set_rule` - Initialize or update the alliance's rule by IPFS hash. 
- `announce` - Make announcement by IPFS hash.
- `nominate_candidacy` - Nominate a non-member to become a Candidate for free.
- `approve_candidate` - Approve a candidate to become an Ally.
- `reject_candidate` - Reject a candidate and slash its deposit.
- `elevate_ally` - Approve an ally to become a Fellow.
- `kick_member` - Kick a member and slash its deposit. 
- `add_blacklist` - Add some items of account and website in the blacklist.
- `remove_blacklist` - Remove some items of account and website from the blacklist.

#### For Members (Only Founders)
- `veto` - Veto on a motion about `set_rule` and `elevate_ally`.

#### For Super Users
- `init_founders` - Initialize the founding members.

License: Apache-2.0
