Collective system: Members of a set of account IDs can make their collective feelings known
through dispatched calls from one of two specialized origins.

The membership can be provided in one of two ways: either directly, using the Root-dispatchable
function `set_members`, or indirectly, through implementing the `ChangeMembers`.
The pallet assumes that the amount of members stays at or below `MaxMembers` for its weight
calculations, but enforces this neither in `set_members` nor in `change_members_sorted`.

A "prime" member may be set to help determine the default vote behavior based on chain
config. If `PrimeDefaultVote` is used, the prime vote acts as the default vote in case of any
abstentions after the voting period. If `MoreThanMajorityThenPrimeDefaultVote` is used, then
abstentations will first follow the majority of the collective voting, and then the prime
member.

Voting happens through motions comprising a proposal (i.e. a dispatchable) plus a
number of approvals required for it to pass and be called. Motions are open for members to
vote on for a minimum period given by `MotionDuration`. As soon as the required number of
approvals is given, the motion is closed and executed. If the number of approvals is not reached
during the voting period, then `close` may be called by any account in order to force the end
the motion explicitly. If a prime member is defined, then their vote is used instead of any
abstentions and the proposal is executed if there are enough approvals counting the new votes.

If there are not, or if no prime member is set, then the motion is dropped without being executed.

License: Apache-2.0
