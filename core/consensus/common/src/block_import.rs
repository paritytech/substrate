
use primitives::{Blake2Hasher, AuthorityId, H256};
use runtime_primitives::traits::{Block as BlockT, DigestItemFor, Header, As};
use runtime_primitives::Justification;
use runtime_primitives::generic::BlockId;

use client::backend;
use client::client::{BlockOrigin, ImportResult, PrePostHeader, Client};
use client::blockchain::{self, HeaderBackend};
use client::call_executor::CallExecutor;
use client::runtime_api::TaggedTransactionQueue;

use client::error::Error;

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

impl<B, E, Block, RA> BlockImport<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Clone + Send + Sync,
	Block: BlockT<Hash=H256>,
	RA: TaggedTransactionQueue<Block>
{
	type Error = Error;

	/// Import a checked and validated block
	fn import_block(
		&self,
		import_block: ImportBlock<Block>,
		new_authorities: Option<Vec<AuthorityId>>,
	) -> Result<ImportResult, Self::Error> {
		use runtime_primitives::traits::Digest;

		let ImportBlock {
			origin,
			header,
			justification,
			post_digests,
			body,
			finalized,
			auxiliary,
		} = import_block;
		let parent_hash = header.parent_hash().clone();

		match self.backend().blockchain().status(BlockId::Hash(parent_hash))? {
			blockchain::BlockStatus::InChain => {},
			blockchain::BlockStatus::Unknown => return Ok(ImportResult::UnknownParent),
		}

		let import_headers = if post_digests.is_empty() {
			PrePostHeader::Same(header)
		} else {
			let mut post_header = header.clone();
			for item in post_digests {
				post_header.digest_mut().push(item);
			}
			PrePostHeader::Different(header, post_header)
		};

		let hash = import_headers.post().hash();
		let _import_lock = self.import_lock().lock();
		let height: u64 = import_headers.post().number().as_();
		*self.importing_block().write() = Some(hash);

		let result = self.execute_and_import_block(
			origin,
			hash,
			import_headers,
			justification,
			body,
			new_authorities,
			finalized,
			auxiliary,
		);

		*self.importing_block().write() = None;
		telemetry!("block.import";
			"height" => height,
			"best" => ?hash,
			"origin" => ?origin
		);
		result.map_err(|e| e.into())
	}
}

