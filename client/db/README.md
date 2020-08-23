Client backend that is backed by a database.

# Canonicality vs. Finality

Finality indicates that a block will not be reverted, according to the consensus algorithm,
while canonicality indicates that the block may be reverted, but we will be unable to do so,
having discarded heavy state that will allow a chain reorganization.

Finality implies canonicality but not vice-versa.

License: GPL-3.0-or-later WITH Classpath-exception-2.0