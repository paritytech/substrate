Statement store is an off-chain data-store for signed statements accessible via RPC and OCW.

Nodes hold a number of statements with a proof of authenticity owing to an account ID. OCWs can place items in the data-store (with valid signatures) for any accounts whose keys they control. Users can also submit pre-signed statements via RPC. Statements can also be submitted from on-chain logic through an on-chain event.

A new system event `NewStatement` is added to the runtime. This event allows any account on-chain to declare that they want to make a statement for the store. Within the node store and for broadcasting, the statement would be accompanied with the hash of the block and index of the event within it, essentially taking the place of a real signature.

Statements comprise an optional proof of authenticity (e.g. a signature) and a number of fields. For statements without a proof, nodes would gossip statements randomly with a rate-limiter to minimise the chance of being overrun by a misbehaving node. These will generally be disregarded by nodes unless they are gossiped by several different peers or if a peer pays for it somehow (e.g. gossiping something valuable).

Each field is effectively a key/value pair. Fields must be sorted and the same field type may not be repeated. Depending on which keys are present, clients may index the message for ease of retrieval.

Formally, `Statement` is equivalent to the type `Vec<Field>` and `Field` is the SCALE-encoded enumeration:
- 0: `AuthenticityProof(Proof)`: The signature of the message. For cryptography where the public key cannot be derived from the signature together with the message data, then this will also include the signer's public key. The message data is all fields of the messages fields except the signature concatenated together *without the length prefix that a `Vec` would usually imply*. This is so that the signature can be derived without needing to re-encode the statement.
- 1: `DecryptionKey([u8; 32])`: The decryption key identifier which should be used to decrypt the statement's data. In the absense of this field `Data` should be treated as not encrypted.
- 2: `Priority(u32)`: Priority specifier. Higher priority statements should be kept around at the cost of lower priority statements if multiple statements from the same sender are competing for persistence or transport. Nodes should disregard when considering unsigned statements.
- 3: `Channel([u8; 32])`: The channel identifier. Only one message of a given channel should be retained at once (the one of highest priority). Nodes should disregard when considering unsigned statements.
- 4: `Topic1([u8; 32]))`: First topic identifier.
- 5: `Topic2([u8; 32]))`: Second topic identifier.
- 6: `Topic3([u8; 32]))`: Third topic identifier.
- 7: `Topic4([u8; 32]))`: Fourth topic identifier.
- 8: `Data(Vec<u8>)`: General data segment. No special meaning.

`Proof` is defined as the SCALE-encoded enumeration:
- 0: `Sr25519 { signature: [u8; 64], signer: [u8; 32] }`
- 1: `Ed25519 { signature: [u8; 64], signer: [u8; 32] )`
- 2: `Secp256k1Ecdsa { signature: [u8; 65], signer: [u8; 33] )`
- 3: `OnChain { who: [u8; 32], block_hash: [u8; 32], event_index: u64 }`

### Potential uses

Potential use-cases are various and include:
- ring-signature aggregation;
- messaging;
- state-channels;
- deferral of the initial "advertising" phase of multi-party transactions;
- publication of preimage data whose hash is referenced on-chain;
- effective transferal of fee payment to a second-party.


License: Apache-2.0
