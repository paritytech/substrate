Aura (Authority-round) consensus in substrate.

Aura works by having a list of authorities A who are expected to roughly
agree on the current time. Time is divided up into discrete slots of t
seconds each. For each slot s, the author of that slot is A[s % |A|].

The author is allowed to issue one block but not more during that slot,
and it will be built upon the longest valid chain that has been seen.

Blocks from future steps will be either deferred or rejected depending on how
far in the future they are.

NOTE: Aura itself is designed to be generic over the crypto used.

License: GPL-3.0-or-later WITH Classpath-exception-2.0