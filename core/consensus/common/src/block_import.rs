
use primitives::AuthorityId;
use runtime_primitives::traits::{Block as BlockT, DigestItemFor};
use runtime_primitives::Justification;

/// Block import result.
#[derive(Debug)]
pub enum ImportResult {
	/// Added to the import queue.
	Queued,
	/// Already in the import queue.
	AlreadyQueued,
	/// Already in the blockchain.
	AlreadyInChain,
	/// Block or parent is known to be bad.
	KnownBad,
	/// Block parent is not in the chain.
	UnknownParent,
}

/// Block data origin.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BlockOrigin {
	/// Genesis block built into the client.
	Genesis,
	/// Block is part of the initial sync with the network.
	NetworkInitialSync,
	/// Block was broadcasted on the network.
	NetworkBroadcast,
	/// Block that was received from the network and validated in the consensus process.
	ConsensusBroadcast,
	/// Block that was collated by this node.
	Own,
	/// Block was imported from a file.
	File,
}

/// Data required to import a Block
pub struct ImportBlock<Block: BlockT> {
	/// Origin of the Block
	pub origin: BlockOrigin,
	/// The header, without consensus post-digests applied. This should be in the same
	/// state as it comes out of the runtime.
	///
	/// Consensus engines which alter the header (by adding post-runtime digests)
	/// should strip those off in the initial verification process and pass them
	/// via the `post_digests` field. During block authorship, they should
	/// not be pushed to the header directly.
	///
	/// The reason for this distinction is so the header can be directly
	/// re-executed in a runtime that checks digest equivalence -- the
	/// post-runtime digests are pushed back on after.
	pub header: Block::Header,
	/// Justification provided for this block from the outside:.
	pub justification: Justification,
	/// Digest items that have been added after the runtime for external
	/// work, like a consensus signature.
	pub post_digests: Vec<DigestItemFor<Block>>,
	/// Block's body
	pub body: Option<Vec<Block::Extrinsic>>,
	/// Is this block finalized already?
	/// `true` implies instant finality.
	pub finalized: bool,
	/// Auxiliary consensus data produced by the block.
	/// Contains a list of key-value pairs. If values are `None`, the keys
	/// will be deleted.
	pub auxiliary: Vec<(Vec<u8>, Option<Vec<u8>>)>,
}

impl<Block: BlockT> ImportBlock<Block> {
	/// Deconstruct the justified header into parts.
	pub fn into_inner(self)
		-> (
			BlockOrigin,
			<Block as BlockT>::Header,
			Justification,
			Vec<DigestItemFor<Block>>,
			Option<Vec<<Block as BlockT>::Extrinsic>>,
			bool,
			Vec<(Vec<u8>, Option<Vec<u8>>)>,
		) {
		(
			self.origin,
			self.header,
			self.justification,
			self.post_digests,
			self.body,
			self.finalized,
			self.auxiliary,
		)
	}
}



/// Block import trait.
pub trait BlockImport<B: BlockT> {
	type Error: ::std::error::Error + Send + 'static;
	/// Import a Block alongside the new authorities valid form this block forward
	fn import_block(&self,
		block: ImportBlock<B>,
		new_authorities: Option<Vec<AuthorityId>>
	) -> Result<ImportResult, Self::Error>;
}