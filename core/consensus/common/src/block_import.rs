
use primitives::{Blake2Hasher, AuthorityId, H256};
use runtime_primitives::traits::{Block as BlockT, DigestItemFor, Header, As};
use runtime_primitives::Justification;
use runtime_primitives::generic::BlockId;

use state_machine::{ExecutionManager, ExecutionStrategy};

use client::backend::{self, BlockImportOperation};
use client::{CallExecutor, BlockOrigin, PrePostHeader, Client, FinalityNotification, BlockImportNotification};
use client::blockchain::{self, HeaderBackend};
use client::runtime_api::TaggedTransactionQueue;

use client::error::Error;

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

	fn execute_and_import_block(
		&self,
		origin: BlockOrigin,
		hash: B::Hash,
		import_headers: PrePostHeader<B::Header>,
		justification: Justification,
		body: Option<Vec<B::Extrinsic>>,
		authorities: Option<Vec<AuthorityId>>,
		finalized: bool,
		aux: Vec<(Vec<u8>, Option<Vec<u8>>)>,
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

	fn execute_and_import_block(
		&self,
		origin: BlockOrigin,
		hash: Block::Hash,
		import_headers: PrePostHeader<Block::Header>,
		justification: Justification,
		body: Option<Vec<Block::Extrinsic>>,
		authorities: Option<Vec<AuthorityId>>,
		finalized: bool,
		aux: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	) -> Result<ImportResult, Self::Error> where
		RA: TaggedTransactionQueue<Block>,
		E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone,
	{
		let parent_hash = import_headers.post().parent_hash().clone();
		match self.backend().blockchain().status(BlockId::Hash(hash))? {
			blockchain::BlockStatus::InChain => return Ok(ImportResult::AlreadyInChain),
			blockchain::BlockStatus::Unknown => {},
		}

		let (last_best, last_best_number) = {
			let info = self.backend().blockchain().info()?;
			(info.best_hash, info.best_number)
		};

		// this is a fairly arbitrary choice of where to draw the line on making notifications,
		// but the general goal is to only make notifications when we are already fully synced
		// and get a new chain head.
		let make_notifications = match origin {
			BlockOrigin::NetworkBroadcast | BlockOrigin::Own | BlockOrigin::ConsensusBroadcast => true,
			BlockOrigin::Genesis | BlockOrigin::NetworkInitialSync | BlockOrigin::File => false,
		};

		// ensure parent block is finalized to maintain invariant that
		// finality is called sequentially.
		if finalized {
			self.apply_finality(parent_hash, last_best, make_notifications)?;
		}

		let tags = self.transaction_tags(parent_hash, &body)?;
		let mut transaction = self.backend().begin_operation(BlockId::Hash(parent_hash))?;
		let (storage_update, changes_update, storage_changes) = match transaction.state()? {
			Some(transaction_state) => {
				let mut overlay = Default::default();
				let mut r = self.executor().call_at_state(
					transaction_state,
					&mut overlay,
					"execute_block",
					&<Block as BlockT>::new(import_headers.pre().clone(), body.clone().unwrap_or_default()).encode(),
					match (origin, self.block_execution_strategy()) {
						(BlockOrigin::NetworkInitialSync, _) | (_, ExecutionStrategy::NativeWhenPossible) =>
							ExecutionManager::NativeWhenPossible,
						(_, ExecutionStrategy::AlwaysWasm) => ExecutionManager::AlwaysWasm,
						_ => ExecutionManager::Both(|wasm_result, native_result| {
							let header = import_headers.post();
							warn!("Consensus error between wasm and native block execution at block {}", hash);
							warn!("   Header {:?}", header);
							warn!("   Native result {:?}", native_result);
							warn!("   Wasm result {:?}", wasm_result);
							telemetry!("block.execute.consensus_failure";
								"hash" => ?hash,
								"origin" => ?origin,
								"header" => ?header
							);
							wasm_result
						}),
					},
				);
				let (_, storage_update, changes_update) = r?;
				overlay.commit_prospective();
				(Some(storage_update), Some(changes_update), Some(overlay.into_committed()))
			},
			None => (None, None, None)
		};

		// TODO: non longest-chain rule.
		let is_new_best = finalized || import_headers.post().number() > &last_best_number;
		let leaf_state = if finalized {
			::backend::NewBlockState::Final
		} else if is_new_best {
			::backend::NewBlockState::Best
		} else {
			::backend::NewBlockState::Normal
		};

		trace!("Imported {}, (#{}), best={}, origin={:?}", hash, import_headers.post().number(), is_new_best, origin);

		transaction.set_block_data(
			import_headers.post().clone(),
			body,
			Some(justification),
			leaf_state,
		)?;

		if let Some(authorities) = authorities {
			transaction.update_authorities(authorities);
		}
		if let Some(storage_update) = storage_update {
			transaction.update_storage(storage_update)?;
		}
		if let Some(Some(changes_update)) = changes_update {
			transaction.update_changes_trie(changes_update)?;
		}

		transaction.set_aux(aux)?;
		self.backend().commit_operation(transaction)?;

		if make_notifications {
			if let Some(storage_changes) = storage_changes {
				// TODO [ToDr] How to handle re-orgs? Should we re-emit all storage changes?
				self.storage_notifications().lock()
					.trigger(&hash, storage_changes);
			}

			if finalized {
				let notification = FinalityNotification::<Block> {
					hash,
					header: import_headers.post().clone(),
				};

				self.finality_notification_sinks().lock()
					.retain(|sink| sink.unbounded_send(notification.clone()).is_ok());
			}

			let notification = BlockImportNotification::<Block> {
				hash,
				origin,
				header: import_headers.into_post(),
				is_new_best,
				tags,
			};

			self.import_notification_sinks().lock()
				.retain(|sink| sink.unbounded_send(notification.clone()).is_ok());
		}

		Ok(ImportResult::Queued)
	}
}

