# Ranked collective system.

This is a membership pallet providing a `Tally` implementation ready for use with polling
systems such as the Referenda pallet. Members each have a rank, with zero being the lowest.
There is no complexity limitation on either the number of members at a rank or the number of
ranks in the system thus allowing potentially public membership. A member of at least a given
rank can be selected at random in O(1) time, allowing for various games to constructed using
this as a primitive. Members may only be promoted and demoted by one rank at a time, however
all operations (save one) are O(1) in complexity. The only operation which is not O(1) is the
`remove_member` since they must be removed from all ranks from the present down to zero.

Different ranks have different voting power, and are able to vote in different polls. In general
rank privileges are cumulative. Higher ranks are able to vote in any polls open to lower ranks.
Similarly, higher ranks always have at least as much voting power in any given poll as lower
ranks.

Two `Config` trait items control these "rank privileges": `MinRankOfClass` and `VoteWeight`.
The first controls which ranks are allowed to vote on a particular class of poll. The second
controls the weight of a vote given the voters rank compared to the minimum rank of the poll.

An origin control, `EnsureRank`, ensures that the origin is a member of the collective of at
least a particular rank.
