Polite gossiping.

This crate provides gossiping capabilities on top of a network.

Gossip messages are separated by two categories: "topics" and consensus engine ID.
The consensus engine ID is sent over the wire with the message, while the topic is not,
with the expectation that the topic can be derived implicitly from the content of the
message, assuming it is valid.

Topics are a single 32-byte tag associated with a message, used to group those messages
in an opaque way. Consensus code can invoke `broadcast_topic` to attempt to send all messages
under a single topic to all peers who don't have them yet, and `send_topic` to
send all messages under a single topic to a specific peer.

# Usage

- Implement the `Network` trait, representing the low-level networking primitives. It is
  already implemented on `sc_network::NetworkService`.
- Implement the `Validator` trait. See the section below.
- Decide on a `ConsensusEngineId`. Each gossiping protocol should have a different one.
- Build a `GossipEngine` using these three elements.
- Use the methods of the `GossipEngine` in order to send out messages and receive incoming
  messages.

# What is a validator?

The primary role of a `Validator` is to process incoming messages from peers, and decide
whether to discard them or process them. It also decides whether to re-broadcast the message.

The secondary role of the `Validator` is to check if a message is allowed to be sent to a given
peer. All messages, before being sent, will be checked against this filter.
This enables the validator to use information it's aware of about connected peers to decide
whether to send messages to them at any given moment in time - In particular, to wait until
peers can accept and process the message before sending it.

Lastly, the fact that gossip validators can decide not to rebroadcast messages
opens the door for neighbor status packets to be baked into the gossip protocol.
These status packets will typically contain light pieces of information
used to inform peers of a current view of protocol state.

License: GPL-3.0-or-later WITH Classpath-exception-2.0